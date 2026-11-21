/**
 * Tests for Polygon.prototype.offset (constant-distance contour offset / kerf compensation)
 */
import { expect } from 'chai';
import Flatten from '../index';
import {Polygon, Circle, Point} from '../index';

const closeTo = (actual, expected, tolerance = 0.01) => {
    expect(Math.abs(actual - expected)).to.be.at.most(tolerance * Math.abs(expected),
        `expected ${actual} to be within ${tolerance * 100}% of ${expected}`);
};

const square = () => new Polygon([[0,0],[10,0],[10,10],[0,10]]);

const holedSquare = () => {
    let polygon = new Polygon();
    polygon.addFace([[0,0],[10,0],[10,10],[0,10]]);
    polygon.addFace([[4,4],[4,6],[6,6],[6,4]]);    // 2x2 hole, opposite orientation
    return polygon;
};

describe('Polygon.offset', function () {
    it('should exist on Polygon.prototype', function () {
        expect(Polygon.prototype.offset).to.be.a('function');
    });

    describe('join types and areas', function () {
        it('expands a square with round joins: area = 100 + 80 + 4*pi', function () {
            let offset = square().offset(2);
            closeTo(offset.area(), 100 + 80 + 4 * Math.PI);
        });
        it('expands a square with miter joins: area = 14x14 = 196', function () {
            let offset = square().offset(2, {join: 'miter'});
            closeTo(offset.area(), 196);
        });
        it('expands a square with bevel joins: area = 196 - 8 = 188', function () {
            let offset = square().offset(2, {join: 'bevel'});
            closeTo(offset.area(), 188);
        });
        it('shrinks a square by 2: area = 6x6 = 36', function () {
            let offset = square().offset(-2);
            closeTo(offset.area(), 36);
        });
        it('falls back to bevel when miter limit exceeded', function () {
            let spike = new Polygon([[0,0],[10,0],[5,0.5]]);
            let bevelArea = spike.offset(1, {join: 'bevel'}).area();
            let limitedArea = spike.offset(1, {join: 'miter', miterLimit: 1}).area();
            let miterArea = spike.offset(1, {join: 'miter', miterLimit: 100}).area();
            closeTo(limitedArea, bevelArea, 0.001);
            expect(miterArea).to.be.greaterThan(bevelArea);
        });
    });

    describe('holes', function () {
        it('shrinks holes when expanding', function () {
            /* outer: 100 + 40*0.5 + pi*0.25, hole 2x2 -> 1x1 rounded: pi/4 */
            let offset = holedSquare().offset(0.5);
            closeTo(offset.area(), 120);
        });
        it('grows holes when shrinking', function () {
            /* outer 10x10 -> 8x8 = 64, hole 2x2 -> 4x4 rounded: 12 + pi */
            let offset = holedSquare().offset(-1);
            closeTo(offset.area(), 64 - 12 - Math.PI);
        });
        it('removes a hole that shrinks to nothing', function () {
            let offset = holedSquare().offset(1);
            expect(offset.faces.size).to.equal(1);
            closeTo(offset.area(), 100 + 40 + Math.PI);
        });
        it('returns an empty polygon when a hole consumes the whole polygon', function () {
            let offset = holedSquare().offset(-6);
            expect(offset.isEmpty()).to.be.true;
            expect(offset.area()).to.equal(0);
        });
        it('returns an empty polygon when outer loop collapses', function () {
            let offset = square().offset(-6);
            expect(offset.isEmpty()).to.be.true;
        });
    });

    describe('concave polygons', function () {
        it('offsets an L-shape into a single connected polygon with band area', function () {
            let L = new Polygon([[0,0],[20,0],[20,10],[10,10],[10,20],[0,20]]);
            let offset = L.offset(1);
            expect(offset.faces.size).to.equal(1);
            expect(offset.isValid()).to.be.true;
            /* area 300 + band 79 (perimeter 80 minus reflex overlap 1) + 5 convex quarter arcs */
            closeTo(offset.area(), 300 + 79 + 5 * Math.PI / 4);
        });
        it('bridges a narrow slot that closes up when expanding', function () {
            let slot = new Polygon([[0,0],[10,0],[10,10],[9.5,10],[9.5,2],[8,2],[8,10],[0,10]]);
            let offset = slot.offset(1);
            expect(offset.isValid()).to.be.true;
            expect(offset.faces.size).to.equal(1);
        });
    });

    describe('zero distance', function () {
        it('returns a geometrically equal new polygon', function () {
            let original = holedSquare();
            let offset = original.offset(0);
            expect(offset).to.not.equal(original);
            expect(offset.area()).to.equal(original.area());
            expect(offset.vertices.length).to.equal(original.vertices.length);
            for (let i = 0; i < original.vertices.length; i++) {
                expect(offset.vertices[i].equalTo(original.vertices[i])).to.be.true;
            }
        });
    });

    describe('round join approximation', function () {
        it('segments option affects the number of points', function () {
            let coarse = square().offset(1, {segments: 2});
            let fine = square().offset(1, {segments: 16});
            expect(coarse.vertices.length).to.be.greaterThan(4);
            expect(fine.vertices.length).to.be.greaterThan(coarse.vertices.length);
        });
        it('keeps join vertices on the theoretical arc within tolerance', function () {
            let segments = 8;
            let distance = 2;
            let offset = square().offset(distance, {segments});
            let tolerance = ((Math.PI / 2) * distance / segments) / 10;
            /* every vertex near a corner of the square is a round join vertex */
            for (let corner of [[10,0],[10,10],[0,10],[0,0]]) {
                let joinVertices = offset.vertices.filter(v =>
                    Math.hypot(v.x - corner[0], v.y - corner[1]) < 3 * distance);
                expect(joinVertices.length).to.be.greaterThan(2);
                for (let v of joinVertices) {
                    let deviation = Math.abs(Math.hypot(v.x - corner[0], v.y - corner[1]) - distance);
                    expect(deviation).to.be.at.most(tolerance);
                }
            }
        });
    });

    describe('invalid parameters', function () {
        it('throws on non-finite distance', function () {
            expect(() => square().offset(NaN)).to.throw(/invalid distance/);
            expect(() => square().offset(Infinity)).to.throw(/invalid distance/);
            expect(() => square().offset('2')).to.throw(/invalid distance/);
        });
        it('throws on unknown join type', function () {
            expect(() => square().offset(1, {join: 'square'})).to.throw(/unknown join type/);
        });
        it('throws on invalid segments', function () {
            expect(() => square().offset(1, {segments: 0})).to.throw(/invalid segments/);
            expect(() => square().offset(1, {segments: -3})).to.throw(/invalid segments/);
        });
    });

    describe('arcs and circles', function () {
        it('offsets a circle into a bigger circle', function () {
            let circle = new Polygon(new Circle(new Point(0,0), 10));
            closeTo(circle.offset(2).area(), Math.PI * 144);
            closeTo(circle.offset(-2).area(), Math.PI * 64);
        });
    });

    describe('performance', function () {
        it('offsets a 10k-vertex contour in less than a second', function () {
            this.timeout(10000);
            let n = 10000;
            let contour = [];
            for (let i = 0; i < n; i++) {
                let angle = 2 * Math.PI * i / n;
                let r = 100 + 5 * Math.sin(20 * angle);
                contour.push([r * Math.cos(angle), r * Math.sin(angle)]);
            }
            let polygon = new Polygon(contour);
            let start = Date.now();
            let offset = polygon.offset(2);
            let elapsed = Date.now() - start;
            expect(elapsed).to.be.below(1000);
            expect(offset.isValid()).to.be.true;
        });
    });
});
