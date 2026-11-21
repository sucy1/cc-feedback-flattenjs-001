/**
 * Created by Alex Bol on 3/15/2017.
 */


"use strict";

import Flatten from '../flatten';
import {ray_shoot} from "../algorithms/ray_shooting";
import * as Intersection from "../algorithms/intersection";
import * as Relations from "../algorithms/relation";
import {
    addToIntPoints, calculateInclusionFlags, filterDuplicatedIntersections,
    getSortedArray, initializeInclusionFlags, insertBetweenIntPoints,
    splitByIntersections
} from "../data_structures/smart_intersections";
import {Multiline} from "./multiline";
import {intersectEdge2Edge} from "../algorithms/intersection";
import * as BooleanOperations from "../algorithms/boolean_op";
import {INSIDE, BOUNDARY, ORIENTATION} from "../utils/constants";
import {convertToString} from "../utils/attributes";
import {Matrix} from "./matrix";

const OFFSET_JOINS = ["round", "miter", "bevel"];

/**
 * Return shape offset by delta along its left normal (delta < 0 offsets to the right).
 * Segments are translated; arcs keep center and angles and change radius.
 * Returns null when the shape collapses (arc radius shrinks to zero or less)
 * @param {Segment|Arc} shape
 * @param {number} delta
 * @returns {Segment|Arc|null}
 */
function offsetEdgeShape(shape, delta) {
    if (shape instanceof Flatten.Segment) {
        let normal = shape.tangentInStart().rotate90CCW().multiply(delta);
        return shape.translate(normal);
    }
    if (shape instanceof Flatten.Arc) {
        /* For a CCW arc the left normal points to the center, for a CW arc away from it */
        let newR = shape.counterClockwise ? shape.r - delta : shape.r + delta;
        if (!(newR > 0)) {
            return null;    // arc collapsed to its center
        }
        return new Flatten.Arc(shape.pc.clone(), newR, shape.startAngle, shape.endAngle, shape.counterClockwise);
    }
    return null;
}

/**
 * Intersection point of the tangent line of shape1 at its end
 * with the tangent line of shape2 at its start. Returns undefined if (near) parallel
 */
function tangentTrimPoint(shape1, shape2) {
    /* tangentInEnd points from end to start: invert to get the direction of travel */
    let t1 = shape1.tangentInEnd().invert();
    let t2 = shape2.tangentInStart();
    let cross = t1.cross(t2);
    if (Flatten.Utils.EQ_0(cross)) {
        return undefined;
    }
    let p1 = shape1.end;
    let p2 = shape2.start;
    let s = ((p2.x - p1.x) * t2.y - (p2.y - p1.y) * t2.x) / cross;
    return new Flatten.Point(p1.x + s * t1.x, p1.y + s * t1.y);
}

/**
 * Return copy of the shape with its end moved to pt (segment or arc)
 */
function setShapeEnd(shape, pt) {
    if (shape instanceof Flatten.Segment) {
        return new Flatten.Segment(shape.start, pt);
    }
    let endAngle = Math.atan2(pt.y - shape.pc.y, pt.x - shape.pc.x);
    return new Flatten.Arc(shape.pc.clone(), shape.r, shape.startAngle, endAngle, shape.counterClockwise);
}

/**
 * Return copy of the shape with its start moved to pt (segment or arc)
 */
function setShapeStart(shape, pt) {
    if (shape instanceof Flatten.Segment) {
        return new Flatten.Segment(pt, shape.end);
    }
    let startAngle = Math.atan2(pt.y - shape.pc.y, pt.x - shape.pc.x);
    return new Flatten.Arc(shape.pc.clone(), shape.r, startAngle, shape.endAngle, shape.counterClockwise);
}

/**
 * Points approximating the round join arc of radius r centered at vertex v,
 * from p1 to p2, turning counterclockwise when ccw is true.
 * Returns interior points only (p1 and p2 excluded).
 * The join is approximated with at least `segments` chords per 90 degrees,
 * and enough chords to keep chordal deviation within (PI/2 * r / segments) / 10
 */
function roundJoinPoints(v, p1, p2, r, ccw, segments) {
    let a1 = Math.atan2(p1.y - v.y, p1.x - v.x);
    let a2 = Math.atan2(p2.y - v.y, p2.x - v.x);
    let sweep = ccw ? a2 - a1 : a1 - a2;
    sweep = ((sweep % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI);
    if (Flatten.Utils.EQ_0(sweep)) {
        return [];
    }
    let tolerance = (Math.PI / 2) / (10 * segments);    // chordal deviation tolerance / r
    let maxStep = 2 * Math.acos(Math.max(-1, 1 - tolerance));
    let k = Math.max(1, Math.ceil(segments * sweep / (Math.PI / 2)), Math.ceil(sweep / maxStep));
    let points = [];
    for (let j = 1; j < k; j++) {
        let ang = ccw ? a1 + sweep * j / k : a1 - sweep * j / k;
        points.push(new Flatten.Point(v.x + r * Math.cos(ang), v.y + r * Math.sin(ang)));
    }
    return points;
}

/**
 * Build the offset shapes of the edges of a face, paired with the vertex
 * that joins each shape to the next surviving one.
 * delta is the signed displacement along the left normal of every edge
 */
function buildOffsetItems(face, delta) {
    let edges = [...face];
    let n = edges.length;
    let offShapes = edges.map(edge => offsetEdgeShape(edge.shape, delta));

    /* Collect surviving offset shapes and the vertex joining each to the next survivor */
    let items = [];
    for (let i = 0; i < n; i++) {
        if (offShapes[i] === null) continue;
        let joinVertex = edges[i].shape.end;
        let j = (i + 1) % n;
        while (offShapes[j] === null) {
            /* Join across collapsed edges around the collapsed arc center */
            joinVertex = edges[j].shape instanceof Flatten.Arc ? edges[j].shape.pc : edges[j].shape.end;
            j = (j + 1) % n;
        }
        items.push({shape: offShapes[i], joinVertex});
    }
    return items;
}

/**
 * Join offset items into a closed loop of shapes.
 * Returns {shapes} with the loop, or {consumed} with the indices of offset edges
 * eaten by trims from both sides (the offset collapsed across them)
 */
function buildLoopShapes(items, delta, join, miterLimit, segments) {
    let m = items.length;

    /* First pass: compute trims at reflex vertices and join shapes at convex vertices */
    let endTrim = new Array(m).fill(undefined);
    let startTrim = new Array(m).fill(undefined);
    let joinShapes = new Array(m).fill(null).map(() => []);
    for (let i = 0; i < m; i++) {
        let cur = items[i].shape;
        let next = items[(i + 1) % m].shape;
        let v = items[i].joinVertex;
        let p1 = cur.end;
        let p2 = next.start;
        if (p1.equalTo(p2)) continue;
        let t1 = cur.tangentInEnd().invert();
        let t2 = next.tangentInStart();
        let cross = t1.cross(t2);
        if (Flatten.Utils.EQ_0(cross)) {
            joinShapes[i].push(new Flatten.Segment(p1, p2));
            continue;
        }
        if (Math.sign(cross) === Math.sign(delta)) {
            /* Reflex corner for this offset direction: trim offset shapes at their intersection */
            let pt = tangentTrimPoint(cur, next);
            if (pt === undefined) {
                joinShapes[i].push(new Flatten.Segment(p1, p2));
            } else {
                endTrim[i] = pt;
                startTrim[(i + 1) % m] = pt;
            }
            continue;
        }
        /* Convex corner: apply join type */
        if (join === "round") {
            let ccw = cross > 0;
            let pts = roundJoinPoints(v, p1, p2, Math.abs(delta), ccw, segments);
            let prev = p1;
            for (let pt of [...pts, p2]) {
                joinShapes[i].push(new Flatten.Segment(prev, pt));
                prev = pt;
            }
        } else if (join === "miter") {
            let pt = tangentTrimPoint(cur, next);
            if (pt !== undefined && pt.distanceTo(v)[0] <= miterLimit * Math.abs(delta)) {
                joinShapes[i].push(new Flatten.Segment(p1, pt), new Flatten.Segment(pt, p2));
            } else {
                joinShapes[i].push(new Flatten.Segment(p1, p2));    // miter limit exceeded: bevel
            }
        } else {    // bevel
            joinShapes[i].push(new Flatten.Segment(p1, p2));
        }
    }

    /* Second pass: instantiate trimmed shapes and joins into one loop */
    let shapes = [];
    let consumed = [];
    for (let i = 0; i < m; i++) {
        let shape = items[i].shape;
        /* An edge consumed by trims from both sides means the offset collapsed
           across it (narrow channel, collapsed hole, offset past the medial axis) */
        if (shape instanceof Flatten.Segment) {
            let tangent = shape.tangentInStart();
            let sStart = startTrim[i] === undefined ? 0 :
                new Flatten.Vector(shape.start, startTrim[i]).dot(tangent);
            let sEnd = endTrim[i] === undefined ? shape.length :
                new Flatten.Vector(shape.start, endTrim[i]).dot(tangent);
            if (!Flatten.Utils.LT(sStart, sEnd)) {
                consumed.push(i);
                continue;
            }
        }
        if (startTrim[i] !== undefined) shape = setShapeStart(shape, startTrim[i]);
        if (endTrim[i] !== undefined) shape = setShapeEnd(shape, endTrim[i]);
        shapes.push(shape, ...joinShapes[i]);
    }
    if (consumed.length > 0) {
        return {consumed};
    }
    /* Drop degenerate zero-length shapes that may appear on exact collapses */
    shapes = shapes.filter(shape => !Flatten.Utils.EQ_0(shape.length));
    return {shapes};
}

/**
 * Build the raw offset loop of a single face as an array of shapes (Segments and Arcs).
 * delta is the signed displacement along the left normal of every edge.
 * Returns null when the loop collapses completely
 */
function offsetFaceLoop(face, delta, join, miterLimit, segments, srcPolygon) {
    let items = buildOffsetItems(face, delta);
    if (items.length === 0) return null;

    /* Iterate: edges consumed by trims or sunk inside the offset region are
       removed and the loop is re-stitched between the survivors */
    let cleanupMode = false;
    while (true) {
        let {shapes, consumed} = buildLoopShapes(items, delta, join, miterLimit, segments);
        if (consumed !== undefined) {
            cleanupMode = true;
        } else if (cleanupMode) {
            /* Remove offset edges that sunk inside the offset region:
               their middle is closer to the source boundary than |delta| */
            consumed = [];
            for (let i = 0; i < items.length; i++) {
                let middle = items[i].shape.middle();
                let dist = Flatten.Distance.point2polygon(middle, srcPolygon)[0];
                if (Flatten.Utils.LT(dist, Math.abs(delta))) {
                    consumed.push(i);
                }
            }
            if (consumed.length === 0) {
                return shapes.length > 0 ? shapes : null;
            }
        } else {
            return shapes.length > 0 ? shapes : null;
        }
        let removed = new Set(consumed);
        items = items.filter((item, i) => !removed.has(i));
        if (items.length < 2) return null;
    }
}

/**
 * Class representing a polygon.<br/>
 * Polygon in FlattenJS is a multipolygon comprised from a set of [faces]{@link Flatten.Face}. <br/>
 * Face, in turn, is a closed loop of [edges]{@link Flatten.Edge}, where edge may be segment or circular arc<br/>
 * @type {Polygon}
 */
export class Polygon {
    /**
     * Constructor creates new instance of polygon. With no arguments new polygon is empty.<br/>
     * Constructor accepts as argument array that define loop of shapes
     * or array of arrays in case of multi polygon <br/>
     * Loop may be defined in different ways: <br/>
     * - array of shapes of type Segment or Arc <br/>
     * - array of points (Flatten.Point) <br/>
     * - array of numeric pairs which represent points <br/>
     * - box or circle object <br/>
     * Alternatively, it is possible to use polygon.addFace method
     * @param {args} - array of shapes or array of arrays
     */
    constructor() {
        /**
         * Container of faces (closed loops), may be empty
         * @type {PlanarSet}
         */
        this.faces = new Flatten.PlanarSet();
        /**
         * Container of edges
         * @type {PlanarSet}
         */
        this.edges = new Flatten.PlanarSet();

        /* It may be array of something that may represent one loop (face) or
         array of arrays that represent multiple loops
         */
        let args = [...arguments];
        if (args.length === 1 &&
            ((args[0] instanceof Array && args[0].length > 0) ||
                args[0] instanceof Flatten.Circle || args[0] instanceof Flatten.Box)) {
            let argsArray = args[0];
            if (args[0] instanceof Array && args[0].every((loop) => {
                return loop instanceof Array
            })) {
                if (argsArray.every(el => {
                    return el instanceof Array && el.length === 2 && typeof (el[0]) === "number" && typeof (el[1]) === "number"
                })) {
                    this.faces.add(new Flatten.Face(this, argsArray));    // one-loop polygon as array of pairs of numbers
                } else {
                    for (let loop of argsArray) {   // multi-loop polygon
                        /* Check extra level of nesting for GeoJSON-style multi polygons */
                        if (loop instanceof Array && loop[0] instanceof Array &&
                            loop[0].every(el => {
                                return el instanceof Array && el.length === 2 && typeof (el[0]) === "number" && typeof (el[1]) === "number"
                            })) {
                            for (let loop1 of loop) {
                                this.faces.add(new Flatten.Face(this, loop1));
                            }
                        } else {
                            this.faces.add(new Flatten.Face(this, loop));
                        }
                    }
                }
            } else {
                this.faces.add(new Flatten.Face(this, argsArray));    // one-loop polygon
            }
        }
    }

    /**
     * (Getter) Returns bounding box of the polygon
     * @returns {Box}
     */
    get box() {
        return [...this.faces].reduce((acc, face) => acc.merge(face.box), new Flatten.Box());
    }

    /**
     * (Getter) Returns array of vertices
     * @returns {Array}
     */
    get vertices() {
        return [...this.faces].flatMap(face => face.vertices);
        // return [...this.edges].map(edge => edge.start);
    }

    /**
     * Create new cloned instance of the polygon
     * @returns {Polygon}
     */
    clone() {
        let polygon = new Polygon();
        for (let face of this.faces) {
            polygon.addFace(face.shapes);
        }
        return polygon;
    }

    /**
     * Create a polygon from an array of polygons. Each polygon is an outer face with all containing inner faces
     * @param polygons
     * @returns {Polygon}
     */
    createFromArray(polygons) {
        const newPolygon = new Polygon();
        polygons.forEach(polygon => [...polygon.faces].forEach(face => newPolygon.addFace(face.shapes)));
        return newPolygon;
    }

    /**
     * Return true is polygon has no edges or faces
     * @returns {boolean}
     */
    isEmpty() {
        return this.edges.size === 0 || this.faces.size === 0;
    }

    /**
     * Return true if polygon is valid for boolean operations
     * Polygon is valid if <br/>
     * 1. All faces are simple polygons (there are no self-intersected polygons) <br/>
     * 2. All faces are orientable and there is no island inside island or hole inside hole - TODO <br/>
     * 3. There is no intersections between faces (excluding touching) - TODO <br/>
     * @returns {boolean}
     */
    isValid() {
        let valid = true;
        // 1. Polygon is invalid if at least one face is not simple
        for (let face of this.faces) {
            if (!face.isSimple(this.edges)) {
                valid = false;
                break;
            }
        }
        // 2. TODO: check if no island inside island and no hole inside hole
        // 3. TODO: check the there is no intersection between faces
        return valid;
    }

    /**
     * Returns area of the polygon. Area of an island will be added, area of a hole will be subtracted
     * @returns {number}
     */
    area() {
        let signedArea = [...this.faces].reduce((acc, face) => acc + face.signedArea(), 0);
        return Math.abs(signedArea);
    }

    /**
     * Add a new face to polygon. Returns added face
     * @param {Point[]|Segment[]|Arc[]|Circle|Box} args -  new face may be create with one of the following ways: <br/>
     * 1) array of points that describe closed path (edges are segments) <br/>
     * 2) array of shapes (segments and arcs) which describe closed path <br/>
     * 3) circle - will be added as counterclockwise arc <br/>
     * 4) box - will be added as counterclockwise rectangle <br/>
     * You can chain method face.reverse() is you need to change direction of the creates face
     * @returns {Face}
     */
    addFace(...args) {
        let face = new Flatten.Face(this, ...args);
        this.faces.add(face);
        return face;
    }

    /**
     * Delete existing face from polygon
     * @param {Face} face Face to be deleted
     * @returns {boolean}
     */
    deleteFace(face) {
        for (let edge of face) {
            this.edges.delete(edge);
        }
        return this.faces.delete(face);
    }

    /**
     * Clear all faces and create new faces from edges
     */
    recreateFaces() {
        // Remove all faces
        this.faces.clear();
        for (let edge of this.edges) {
            edge.face = null;
        }

        // Restore faces
        let first;
        let unassignedEdgeFound = true;
        while (unassignedEdgeFound) {
            unassignedEdgeFound = false;
            for (let edge of this.edges) {
                if (edge.face === null) {
                    first = edge;
                    unassignedEdgeFound = true;
                    break;
                }
            }

            if (unassignedEdgeFound) {
                let last = first;
                do {
                    last = last.next;
                } while (last.next !== first)

                this.addFace(first, last);
            }
        }
    }

    /**
     * Delete chain of edges from the face.
     * @param {Face} face Face to remove chain
     * @param {Edge} edgeFrom Start of the chain of edges to be removed
     * @param {Edge} edgeTo End of the chain of edges to be removed
     */
    removeChain(face, edgeFrom, edgeTo) {
        // Special case: all edges removed
        if (edgeTo.next === edgeFrom) {
            this.deleteFace(face);
            return;
        }
        for (let edge = edgeFrom; edge !== edgeTo.next; edge = edge.next) {
            face.remove(edge);
            this.edges.delete(edge);      // delete from PlanarSet of edges and update index
            if (face.isEmpty()) {
                this.deleteFace(face);    // delete from PlanarSet of faces and update index
                break;
            }
        }
    }

    /**
     * Add point as a new vertex and split edge. Point supposed to belong to an edge.
     * When edge is split, new edge created from the start of the edge to the new vertex
     * and inserted before current edge.
     * Current edge is trimmed and updated.
     * Method returns new edge added. If no edge added, it returns edge before vertex
     * @param {Point} pt Point to be added as a new vertex
     * @param {Edge} edge Edge to be split with new vertex and then trimmed from start
     * @returns {Edge}
     */
    addVertex(pt, edge) {
        let shapes = edge.shape.split(pt);
        // if (shapes.length < 2) return;

        if (shapes[0] === null)   // point incident to edge start vertex, return previous edge
            return edge.prev;

        if (shapes[1] === null)   // point incident to edge end vertex, return edge itself
            return edge;

        let newEdge = new Flatten.Edge(shapes[0]);
        let edgeBefore = edge.prev;

        /* Insert first split edge into linked list after edgeBefore */
        edge.face.insert(newEdge, edgeBefore);

        // Remove old edge from edges container and 2d index
        this.edges.delete(edge);

        // Insert new edge to the edges container and 2d index
        this.edges.add(newEdge);

        // Update edge shape with second split edge keeping links
        edge.shape = shapes[1];

        // Add updated edge to the edges container and 2d index
        this.edges.add(edge);

        return newEdge;
    }

    /**
     * Merge given edge with next edge and remove vertex between them
     * @param {Edge} edge
     */
    removeEndVertex(edge) {
        const edge_next = edge.next
        if (edge_next === edge) return
        edge.face.merge_with_next_edge(edge)
        this.edges.delete(edge_next)
    }

    /**
     * Cut polygon with multiline and return a new polygon
     * The cutting is done by intersection of multiline with edges of the polygon.
     * @param multiline
     * @returns {Polygon}
     */
    cut(multiline) {
        const polygons = this.splitToIslands();
        const result = polygons.flatMap(polygon => polygon._cutSingleIsland(multiline))
            .filter(polygon => polygon.isValid() && polygon.isEmpty() === false);
        return this.createFromArray(result);
    }

    /**
     * Cut polygon with multiline and return a new polygon
     * @param {Multiline} multiline
     * @returns {Polygon}
     */
    _cutSingleIsland(inputMultiline) {
        let newPoly = this.clone()
        const multiline = inputMultiline.clone();

        // smart intersections
        let intersections = {
            int_points1: [],
            int_points2: [],
            int_points1_sorted: [],
            int_points2_sorted: []
        };

        // intersect each edge of multiline with each edge of the polygon
        // and create smart intersections
        for (let edge1 of multiline.edges) {
            for (let edge2 of newPoly.edges) {
                let ip = intersectEdge2Edge(edge1, edge2);
                // for each intersection point
                for (let pt of ip) {
                    addToIntPoints(edge1, pt, intersections.int_points1);
                    addToIntPoints(edge2, pt, intersections.int_points2);
                }
            }
        }

        // No intersections - return a copy of the original polygon
        if (intersections.int_points1.length === 0)
            return newPoly;

        // sort smart intersections
        intersections.int_points1_sorted = getSortedArray(intersections.int_points1);
        intersections.int_points2_sorted = getSortedArray(intersections.int_points2);

        // split by intersection points
        splitByIntersections(multiline, intersections.int_points1_sorted);
        splitByIntersections(newPoly, intersections.int_points2_sorted);

        // filter duplicated intersection points
        filterDuplicatedIntersections(intersections);

        // sort intersection points again after filtering
        intersections.int_points1_sorted = getSortedArray(intersections.int_points1);
        intersections.int_points2_sorted = getSortedArray(intersections.int_points2);

        // initialize inclusion flags for edges of multiline incident to intersections
        initializeInclusionFlags(intersections.int_points1);

        // calculate inclusion flag for edges of multiline incident to intersections
        calculateInclusionFlags(intersections.int_points1, newPoly);

        // filter intersections between two edges that got same inclusion flag
        for (let int_point1 of intersections.int_points1_sorted) {
            if (int_point1.edge_before && int_point1.edge_after &&
                int_point1.edge_before.bv === int_point1.edge_after.bv) {
                intersections.int_points2[int_point1.id] = -1;   // to be filtered out
                int_point1.id = -1;                              // to be filtered out
            }
        }
        intersections.int_points1 = intersections.int_points1.filter( int_point => int_point.id >= 0);
        intersections.int_points2 = intersections.int_points2.filter( int_point => int_point.id >= 0);
        intersections.int_points1.forEach((int_point, index) => { int_point.id = index });
        intersections.int_points2.forEach((int_point, index) => { int_point.id = index });


        // No intersections left after filtering - return a copy of the original polygon
        if (intersections.int_points1.length === 0)
            return newPoly;

        // sort intersection points 3d time after filtering
        intersections.int_points1_sorted = getSortedArray(intersections.int_points1);
        intersections.int_points2_sorted = getSortedArray(intersections.int_points2);

        // Add new inner edges between intersection points
        let int_point1_prev
        let int_point1_curr;
        for (let i = 1; i <  intersections.int_points1_sorted.length; i++) {
            int_point1_curr = intersections.int_points1_sorted[i]
            int_point1_prev = intersections.int_points1_sorted[i-1];
            if (int_point1_curr.edge_before && int_point1_curr.edge_before.bv === INSIDE) {
                let edgeFrom = int_point1_prev.edge_after
                let edgeTo = int_point1_curr.edge_before
                let newEdges = multiline.getChain(edgeFrom, edgeTo)
                insertBetweenIntPoints(intersections.int_points2[int_point1_prev.id], intersections.int_points2[int_point1_curr.id], newEdges);
                newEdges.forEach(edge => newPoly.edges.add(edge))

                newEdges = newEdges.reverse().map(edge => new Flatten.Edge(edge.shape.reverse()))
                for (let k=0; k < newEdges.length-1; k++) {
                    newEdges[k].next = newEdges[k+1]
                    newEdges[k+1].prev = newEdges[k]
                }
                insertBetweenIntPoints(intersections.int_points2[int_point1_curr.id], intersections.int_points2[int_point1_prev.id], newEdges);
                newEdges.forEach(edge => newPoly.edges.add(edge));
            }

        }

        // Recreate faces
        newPoly.recreateFaces();

        return newPoly
    }

    /**
     * A special case of cut() function
     * The return is a polygon cut with line
     * @param {Line} line - cutting line
     * @returns {Polygon} newPoly - resulted polygon
     */
    cutWithLine(line) {
        let multiline = new Multiline([line]);
        return this.cut(multiline);
    }

    /**
     * Offset the polygon boundary by a constant distance, like a laser-cutter
     * kerf compensation. Every edge is shifted along its normal and neighboring
     * offset edges are joined at vertices. <br/>
     * Positive distance expands the polygon (outer faces grow, holes shrink),
     * negative distance shrinks it (outer faces shrink, holes grow).
     * Zero distance returns a geometrically equal new polygon. <br/>
     * When the offset consumes the whole polygon (e.g. a hole grows over its
     * island), an empty polygon is returned.
     * @param {number} distance - offset distance: > 0 to expand, < 0 to shrink
     * @param {Object} [options] - offset options
     * @param {string} [options.join="round"] - join type at convex corners: "round" | "miter" | "bevel"
     * @param {number} [options.miterLimit=4] - max miter length as a multiple of |distance|, otherwise bevel
     * @param {number} [options.segments=8] - number of chords per 90 degrees of a round join
     * @returns {Polygon}
     */
    offset(distance, options = {}) {
        let {join = "round", miterLimit = 4, segments = 8} = options;

        if (typeof distance !== "number" || !Number.isFinite(distance)) {
            throw new Error(`invalid distance: ${distance}`);
        }
        if (!OFFSET_JOINS.includes(join)) {
            throw new Error(`unknown join type: ${join}`);
        }
        if (typeof segments !== "number" || !Number.isFinite(segments) || segments < 1) {
            throw new Error(`invalid segments: ${segments}`);
        }
        if (Flatten.Utils.EQ_0(distance)) {
            return this.clone();
        }
        if (this.isEmpty()) {
            return new Polygon();
        }

        /* Orientation of the outer faces: orientation of the largest face */
        let dominant = ORIENTATION.NOT_ORIENTABLE;
        let maxArea = 0;
        for (let face of this.faces) {
            let area = Math.abs(face.signedArea());
            if (area > maxArea) {
                maxArea = area;
                dominant = face.orientation();
            }
        }

        /* With consistent orientation the material is always on the left of every
           edge, so a single signed displacement works for outer faces and holes */
        let delta = -distance;

        /* Build raw offset loop for every face; drop loops that collapsed or flipped */
        let loops = [];
        for (let face of this.faces) {
            let shapes = offsetFaceLoop(face, delta, join, miterLimit, segments, this);
            if (shapes === null) continue;
            let loopPolygon = new Polygon(shapes);
            if (loopPolygon.isEmpty()) continue;
            let loopFace = [...loopPolygon.faces][0];
            let signedArea = loopFace.signedArea();
            if (Flatten.Utils.EQ_0(signedArea)) continue;                    // collapsed to zero area
            if (Math.sign(signedArea) !== Math.sign(face.signedArea())) continue;   // flipped: collapsed
            loops.push({polygon: loopPolygon, outer: face.orientation() === dominant});
        }

        let outerLoops = loops.filter(loop => loop.outer);
        let holeLoops = loops.filter(loop => !loop.outer);

        /* No outer boundary survived: the offset consumed the whole polygon */
        if (outerLoops.length === 0) {
            return new Polygon();
        }

        /* Drop outer loops swallowed by a grown hole */
        outerLoops = outerLoops.filter(outer =>
            !holeLoops.some(hole => hole.polygon.contains(outer.polygon.vertices[0])));
        if (outerLoops.length === 0) {
            return new Polygon();
        }
        /* Drop holes that no longer lay inside any outer loop */
        holeLoops = holeLoops.filter(hole =>
            outerLoops.some(outer => outer.polygon.contains(hole.polygon.vertices[0])));

        let newPolygon = new Polygon();
        for (let loop of [...outerLoops, ...holeLoops]) {
            for (let face of loop.polygon.faces) {
                newPolygon.addFace(face.shapes);
            }
        }

        /* Clean possible self-intersections of the raw offset (e.g. small loops
           appearing when opposite walls of a narrow channel expand into each other)
           with a single boolean unify */
        if (!newPolygon.isValid()) {
            try {
                let cleaned = BooleanOperations.unify(newPolygon, newPolygon.clone());
                if (!cleaned.isEmpty()) {
                    let filtered = new Polygon();
                    for (let face of cleaned.faces) {
                        if (!Flatten.Utils.EQ_0(face.signedArea()) &&
                            face.orientation() !== ORIENTATION.NOT_ORIENTABLE) {
                            filtered.addFace(face.shapes);
                        }
                    }
                    if (!filtered.isEmpty()) {
                        newPolygon = filtered;
                    }
                }
            } catch (e) {
                /* keep the raw offset when the boolean cleanup cannot complete */
            }
        }

        return newPolygon;
    }


    /**
     * Returns the first found edge of polygon that contains given point
     * If point is a vertex, return the edge where the point is an end vertex, not a start one
     * @param {Point} pt
     * @returns {Edge}
     */
    findEdgeByPoint(pt) {
        let edge;
        for (let face of this.faces) {
            edge = face.findEdgeByPoint(pt);
            if (edge !== undefined)
                break;
        }
        return edge;
    }

    /**
     * Split polygon into an array of islands with their contained holes.
     * The largest face defines the outer orientation; opposite-oriented faces represent voids.
     * Holes not contained in any island are omitted from the result, without changing
     * their orientation or the input polygon. This method does not clip overlapping faces.
     * @returns {Flatten.Polygon[]}
     */
    splitToIslands() {
        if (this.isEmpty()) return [];      // return empty array if polygon is empty
        let polygons = this.toArray();      // split into array of one-loop polygons
        /* Sort polygons by area in descending order */
        polygons.sort((polygon1, polygon2) => polygon2.area() - polygon1.area());
        /* define orientation of the island by orientation of the first polygon in array */
        let orientation = [...polygons[0].faces][0].orientation();
        /* Create output array from polygons with same orientation as a first polygon (array of islands) */
        let newPolygons = polygons.filter(polygon => [...polygon.faces][0].orientation() === orientation);
        for (let polygon of polygons) {
            let face = [...polygon.faces][0];
            if (face.orientation() === orientation) continue;  // skip same orientation
            /* Proceed with opposite orientation */
            /* Look if any of island polygons contains tested polygon as a hole */
            for (let islandPolygon of newPolygons) {
                if (face.shapes.every(shape => islandPolygon.contains(shape))) {
                    islandPolygon.addFace(face.shapes);      // add polygon as a hole in islandPolygon
                    break;
                }
            }
            // An uncontained hole is a void outside the islands and contributes no filled region.
        }
        return newPolygons;
    }

    /**
     * Rearrange polygon to ensure that all outer faces go first and all inner faces (holes) go after
     * @returns {Polygon}
     */
    rearrange() {
        if (this.faces.size <=1 ) return this.clone()
        const islands = this.splitToIslands()
        const newPolygon = new Polygon()
        islands.forEach(island => {
            island.faces.forEach((face) => newPolygon.addFace(face.shapes))
        })
        return newPolygon
    }

    /**
     * Helper method to get orientation of the polygon as the first face orientation
     * Assume that polygon is properly arranged and the first face is the outer face
     * @returns {Flatten.ORIENTATION.PolygonOrientationType}
     */
    orientation() {
        if (this.isEmpty()) return ORIENTATION.NOT_ORIENTABLE
        return [...this.faces][0].orientation();
    }

    /**
     * Helper method to check if face is outer face of the polygon
     * @param {Flatten.Face} face - face to check
     * @returns {boolean}
     */
    isOuter(face) {
        return face.orientation() === this.orientation();
    }

    /**
     * Helper method to check if a polygon is a multi-polygon (has more than one outer face)
     * @returns {boolean}
     */
    isMultiPolygon() {
        let outerCounter = 0
        this.faces.forEach(face => {
            if (this.isOuter(face)) outerCounter++
        })
        return outerCounter > 1
    }

    /**
     * Reverse orientation of all faces to opposite
     * @returns {Polygon}
     */
    reverse() {
        for (let face of this.faces) {
            face.reverse();
        }
        return this;
    }

    /**
     * Returns true if polygon contains shape: no point of shape lay outside of the polygon,
     * false otherwise
     * @param {Shape} shape - test shape
     * @returns {boolean}
     */
    contains(shape) {
        if (shape instanceof Flatten.Point) {
            let rel = ray_shoot(this, shape);
            return rel === INSIDE || rel === BOUNDARY;
        } else {
            return Relations.cover(this, shape);
        }
    }

    /**
     * Return distance and shortest segment between polygon and other shape as array [distance, shortest_segment]
     * @param {Shape} shape Shape of one of the types Point, Circle, Line, Segment, Arc, Box or Polygon
     * @returns {Number | Segment}
     */
    distanceTo(shape) {
        // let {Distance} = Flatten;

        if (shape instanceof Flatten.Point) {
            let [dist, shortest_segment] = Flatten.Distance.point2polygon(shape, this);
            shortest_segment = shortest_segment.reverse();
            return [dist, shortest_segment];
        }

        if (shape instanceof Flatten.Circle ||
            shape instanceof Flatten.Line ||
            shape instanceof Flatten.Segment ||
            shape instanceof Flatten.Arc) {
            let [dist, shortest_segment] = Flatten.Distance.shape2polygon(shape, this);
            shortest_segment = shortest_segment.reverse();
            return [dist, shortest_segment];
        }

        if (shape instanceof Flatten.Box) {
            return this.distanceTo(new Flatten.Polygon(shape));
        }

        /* this method is bit faster */
        if (shape instanceof Flatten.Polygon) {
            let min_dist_and_segment = [Number.POSITIVE_INFINITY, new Flatten.Segment()];
            let dist, shortest_segment;

            for (let edge of this.edges) {
                // let [dist, shortest_segment] = Distance.shape2polygon(edge.shape, shape);
                let min_stop = min_dist_and_segment[0];
                [dist, shortest_segment] = Flatten.Distance.shape2planarSet(edge.shape, shape.edges, min_stop);
                if (Flatten.Utils.LT(dist, min_stop)) {
                    min_dist_and_segment = [dist, shortest_segment];
                }
            }
            return min_dist_and_segment;
        }
    }

    /**
     * Return array of intersection points between polygon and other shape
     * @param shape Shape of the one of supported types <br/>
     * @returns {Point[]}
     */
    intersect(shape) {
        if (shape instanceof Flatten.Point) {
            return this.contains(shape) ? [shape] : [];
        }

        if (shape instanceof Flatten.Line) {
            return Intersection.intersectLine2Polygon(shape, this);
        }

        if (shape instanceof Flatten.Ray) {
            return Intersection.intersectRay2Polygon(shape, this);
        }

        if (shape instanceof Flatten.Circle) {
            return Intersection.intersectCircle2Polygon(shape, this);
        }

        if (shape instanceof Flatten.Segment) {
            return Intersection.intersectSegment2Polygon(shape, this);
        }

        if (shape instanceof Flatten.Arc) {
            return Intersection.intersectArc2Polygon(shape, this);
        }

        if (shape instanceof Flatten.Polygon) {
            return Intersection.intersectPolygon2Polygon(shape, this);
        }

        if (shape instanceof Flatten.Multiline) {
            return Intersection.intersectMultiline2Polygon(shape, this);
        }
    }

    /**
     * Returns new polygon translated by vector vec
     * @param {Vector} vec
     * @returns {Polygon}
     */
    translate(vec) {
        let newPolygon = new Polygon();
        for (let face of this.faces) {
            newPolygon.addFace(face.shapes.map(shape => shape.translate(vec)));
        }
        return newPolygon;
    }

    /**
     * Return new polygon rotated by given angle around given point
     * If point omitted, rotate around origin (0,0)
     * Positive value of angle defines rotation counterclockwise, negative - clockwise
     * @param {number} angle - rotation angle in radians
     * @param {Point} center - rotation center, default is (0,0)
     * @returns {Polygon} - new rotated polygon
     */
    rotate(angle = 0, center = new Flatten.Point()) {
        let newPolygon = new Polygon();
        for (let face of this.faces) {
            newPolygon.addFace(face.shapes.map(shape => shape.rotate(angle, center)));
        }
        return newPolygon;
    }

    /**
     * Return new polygon with coordinates multiplied by scaling factor
     * @param {number} sx - x-axis scaling factor
     * @param {number} sy - y-axis scaling factor
     * @returns {Polygon}
     */
    scale(sx, sy) {
        let newPolygon = new Polygon();
        for (let face of this.faces) {
            newPolygon.addFace(face.shapes.map(shape => shape.scale(sx, sy)));
        }
        return newPolygon;
    }

    /**
     * Return new polygon transformed using affine transformation matrix
     * @param {Matrix} matrix - affine transformation matrix
     * @returns {Polygon} - new polygon
     */
    transform(matrix = new Flatten.Matrix()) {
        let newPolygon = new Polygon();
        for (let face of this.faces) {
            newPolygon.addFace(face.shapes.map(shape => shape.transform(matrix)));
        }
        return newPolygon;
    }

    /**
     * This method returns an object that defines how data will be
     * serialized when called JSON.stringify() method
     * @returns {Object}
     */
    toJSON() {
        return [...this.faces].map(face => face.toJSON());
    }

    /**
     * Transform all faces into array of polygons
     * @returns {Flatten.Polygon[]}
     */
    toArray() {
        return [...this.faces].map(face => face.toPolygon());
    }

    /**
     * Return string to be assigned to 'd' attribute of <path> element
     * @returns {string}
     */
    dpath() {
        return [...this.faces].reduce((acc, face) => acc + face.svg(), "")
    }

    /**
     * Return string to draw polygon in svg
     * @param attrs  - an object with attributes for svg path element
     * @returns {string}
     */
    svg(attrs = {}) {
        let svgStr = `\n<path ${convertToString({fillRule: "evenodd", fill: "lightcyan", ...attrs})} d="`;
        for (let face of this.faces) {
            svgStr += `\n${face.svg()}` ;
        }
        svgStr += `" >\n</path>`;
        return svgStr;
    }
}

Flatten.Polygon = Polygon;

/**
 * Shortcut method to create new polygon
 */
export const polygon = (...args) => new Flatten.Polygon(...args);
Flatten.polygon = polygon;
