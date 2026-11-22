"use strict";

// Exact interval arithmetic certificate for the two-level Ore calculation.
// Child grid endpoints have denominator 1000.  All Number arithmetic in
// childUpper is integer arithmetic on integers of magnitude less than 10^7.
// Parent boxes and products use BigInt.  No rounded floating-point comparison
// is used.
const grid = 1000;
const childDenominator = 6 * grid * grid;
const childCap = childDenominator / 3;
const childCache = new Map([[grid / 2, childCap]]);

function childUpper(minimumDegree) {
    const minimum = Math.max(grid / 2, Math.min(grid, minimumDegree));
    if (childCache.has(minimum)) return childCache.get(minimum);

    let upper = 0;
    const degreeProduct = minimum * (grid - minimum);

    // c <= 1/2: set r = sqrt(c*s).  Then F <= a*(1-a)+r*r and
    // R <= 2*(1-r)^2.  Each loop iteration bounds one interval for r.
    for (let r = 0; r < grid / 2; r++) {
        const f = degreeProduct + (r + 1) ** 2;
        const R = 2 * (grid - r) ** 2;
        upper = Math.max(upper, Math.min(6 * f, 3 * f + R));
    }

    // c >= 1/2: use rectangles with lower endpoints c,s.  The true
    // degree a is at least max(minimum,c), and the true s is at most
    // min(1-c,1-minimum).  Including excess boundary rectangles is safe.
    for (let c = grid / 2; c < grid; c++) {
        const degree = Math.max(minimum, c);
        const degreeProduct = degree * (grid - degree);
        const sLimit = Math.min(grid - c, grid - minimum);
        for (let s = 0; s <= sLimit; s++) {
            const f = degreeProduct + (c + 1) * (s + 1);
            const R = (grid - c) ** 2 + (grid - s) ** 2;
            upper = Math.max(upper, Math.min(6 * f, 3 * f + R));
        }
    }

    const result = Math.min(childCap, upper);
    childCache.set(minimum, result);
    return result;
}

const scale = 1000n * (1n << 24n);
const scaleSquared = scale * scale;
const denominator = BigInt(childDenominator);
const square = value => value * value;
const endpoint = value => BigInt(value) * (scale / 1000n);

function excludes(box) {
    const [[aLow, aHigh], [cLow, cHigh], [sLow, sHigh]] = box;
    const pHigh = cHigh * sHigh;
    const pLow = cLow * sLow;
    if (12n * pHigh < scaleSquared ||
        100n * pLow > 9n * scaleSquared ||
        5n * (cLow + sLow) > 3n * scale) return true;

    let maximizingDegree = scale / 2n;
    if (maximizingDegree < aLow) maximizingDegree = aLow;
    if (maximizingDegree > aHigh) maximizingDegree = aHigh;
    const F = maximizingDegree * (scale - maximizingDegree) + pHigh;
    const cRemainder = square(scale - cLow);
    const sRemainder = square(scale - sLow);
    if (3n * F < scaleSquared ||
        3n * F + cRemainder + sRemainder < 2n * scaleSquared) return true;

    // G and L here have denominator 3*scale^2.
    const G = 3n * F - scaleSquared;
    const L = 2n * scale * sLow - square(sLow) - G;
    if (L <= 0n) return false;

    const degreeNumerator = BigInt(grid) * aLow * L;
    const degreeDenominator = (L + 2n * G) * (scale - cLow);
    const minimumDegree = Number(degreeNumerator / degreeDenominator);
    const U = BigInt(childUpper(minimumDegree));

    // F + (1/3)*(1-s)^2 + U*(1-c)^2 < 2/3 after clearing denominators.
    return denominator * F + (denominator / 3n) * sRemainder +
        U * cRemainder < (2n * denominator / 3n) * scaleSquared;
}

const start = [[418, 582], [218, 382], [218, 382]]
    .map(([lower, upper]) => [endpoint(lower), endpoint(upper)]);
const pending = [[start, 0]];
let inspected = 0;
let maxDepth = 0;
while (pending.length > 0) {
    const [box, depth] = pending.pop();
    inspected++;
    maxDepth = Math.max(maxDepth, depth);
    if (excludes(box)) continue;
    if (depth === 24) throw Error("Unresolved box: " + box.map(pair => pair.join(",")).join("; "));

    let axis = 0;
    for (let i = 1; i < box.length; i++) {
        if (box[i][1] - box[i][0] > box[axis][1] - box[axis][0]) axis = i;
    }
    const [low, high] = box[axis];
    const middle = (low + high) / 2n;
    const left = box.slice();
    const right = box.slice();
    left[axis] = [low, middle];
    right[axis] = [middle, high];
    pending.push([left, depth + 1], [right, depth + 1]);
}
console.log(JSON.stringify({ inspected, maxDepth, childBounds: childCache.size, unresolved: 0 }));
