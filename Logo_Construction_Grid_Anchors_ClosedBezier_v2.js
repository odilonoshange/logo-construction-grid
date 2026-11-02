/**
 * name: Logo Construction Grid
 */
"use strict";

const { Document } = require("/document.js");
const { Dialog, DialogResult } = require("/dialog.js");
const { UnitType } = require("/units.js");
const { DocumentCommand, AddChildNodesCommandBuilder, InsertionMode, NodeChildType } = require("/commands.js");
const { Selection } = require("/selections.js");
const { PolyCurve, CurveBuilder } = require("/geometry.js");
const { PolyCurveNodeDefinition, ContainerNodeDefinition } = require("/nodes.js");
const { FillDescriptor } = require("/fills.js");
const { LineStyleDescriptor } = require("/linestyle.js");
const { Colour } = require("/colours.js");

const doc = Document.current;
const EPS = 1e-7;
const DEG = Math.PI / 180;

function attachTip(ctrl, text) {
  if (!ctrl || !text) return;
  try { ctrl.description = text; } catch (e) {
    try { ctrl.setDescription(text); } catch (err) {}
  }
}

function isDialogOk(res) {
  if (!res) return false;
  if (res.equals && res.equals(DialogResult.Ok)) return true;
  if (res === DialogResult.Ok || res == DialogResult.Ok) return true;
  if (res.value !== undefined && DialogResult.Ok.value !== undefined && res.value === DialogResult.Ok.value) return true;
  return false;
}

function isEmbeddedDocumentNode(node) {
  if (!node) return false;
  try {
    if (node.isEmbeddedDocumentNode || node[Symbol.toStringTag] === "EmbeddedDocumentNode") return true;
    if (node.embeddedDocumentInterface) return true;
  } catch (e) {}
  return false;
}

function toArray(v) {
  if (!v) return [];
  if (Array.isArray(v)) return v;
  try { if (v.toArray) return v.toArray(); } catch (e) {}
  try { return Array.from(v); } catch (e) {}
  return [];
}

function clamp(v, min, max) {
  return Math.max(min, Math.min(max, v));
}

function makeColorRGBA(r, g, b, a = 255) {
  return Colour.createRGBA8({
    r: clamp(Math.round(r), 0, 255),
    g: clamp(Math.round(g), 0, 255),
    b: clamp(Math.round(b), 0, 255),
    alpha: clamp(Math.round(a), 0, 255)
  });
}

function resolveFillDescriptor(pickerOrColour, fallbackR, fallbackG, fallbackB, fallbackA = 255) {
  let col = null;
  try {
    if (pickerOrColour && pickerOrColour.value) {
      col = pickerOrColour.value;
    } else if (pickerOrColour && typeof pickerOrColour.getAlpha === "function") {
      col = pickerOrColour;
    }
  } catch (e) {}

  if (!col) {
    col = makeColorRGBA(fallbackR, fallbackG, fallbackB, fallbackA);
  }

  try {
    const desc = FillDescriptor.createSolid(col);
    if (desc) return desc;
  } catch (e) {}

  return FillDescriptor.createNone();
}

function collectBeziers(curve) {
  const beziers = [];
  try { for (const bez of curve.beziers) beziers.push(bez); } catch (e) {}
  return beziers;
}

function extractPolyCurvesFromSingleNode(node) {
  try {
    const ci = node.curvesInterface;
    if (!ci || !ci.polyCurve || ci.polyCurve.curveCount === 0) return null;
    const pc = ci.polyCurve.clone();
    pc.transform(node.baseToSpreadTransform);
    return pc;
  } catch (e) { return null; }
}

function extractCompositePolyCurve(rootNodes) {
  const masterPoly = PolyCurve.create();
  let count = 0;

  function traverse(node) {
    if (!node || isEmbeddedDocumentNode(node)) return;

    const directPc = extractPolyCurvesFromSingleNode(node);
    if (directPc && directPc.curveCount > 0) {
      for (let c = 0; c < directPc.curveCount; c++) {
        masterPoly.addCurve(directPc.at(c).clone());
        count++;
      }
      return;
    }

    const children = toArray(node.children);
    for (const child of children) traverse(child);
  }

  for (const n of rootNodes) traverse(n);
  return count > 0 ? masterPoly : null;
}

function makeSmoothCirclePoly(cx, cy, r) {
  const KAPPA = 0.5522847498307936;
  const d = r * KAPPA;
  const cb = CurveBuilder.create();
  cb.beginXY(cx + r, cy);
  cb.addBezierXY(cx + r, cy + d, cx + d, cy + r, cx, cy + r);
  cb.addBezierXY(cx - d, cy + r, cx - r, cy + d, cx - r, cy);
  cb.addBezierXY(cx - r, cy - d, cx - d, cy - r, cx, cy - r);
  cb.addBezierXY(cx + d, cy - r, cx + r, cy - d, cx + r, cy);
  cb.close();
  const pc = PolyCurve.create();
  pc.addCurve(cb.createCurve());
  return pc;
}

function makeSquarePoly(cx, cy, s) {
  const cb = CurveBuilder.create();
  cb.beginXY(cx - s, cy - s);
  cb.lineToXY(cx + s, cy - s);
  cb.lineToXY(cx + s, cy + s);
  cb.lineToXY(cx - s, cy + s);
  cb.close();
  const pc = PolyCurve.create();
  pc.addCurve(cb.createCurve());
  return pc;
}

function makeLinePoly(x1, y1, x2, y2) {
  const cb = CurveBuilder.create();
  cb.beginXY(x1, y1);
  cb.lineToXY(x2, y2);
  const pc = PolyCurve.create();
  pc.addCurve(cb.createCurve());
  return pc;
}

function dist(a, b) {
  if (!a || !b || !Number.isFinite(a.x) || !Number.isFinite(a.y) || !Number.isFinite(b.x) || !Number.isFinite(b.y)) return Infinity;
  return Math.hypot(a.x - b.x, a.y - b.y);
}

function cross(ax, ay, bx, by) { return ax * by - ay * bx; }

function cubicPoint(b, t) {
  const mt = 1 - t, mt2 = mt * mt, t2 = t * t;
  return {
    x: mt2 * mt * b.start.x + 3 * mt2 * t * b.c1.x + 3 * mt * t2 * b.c2.x + t2 * t * b.end.x,
    y: mt2 * mt * b.start.y + 3 * mt2 * t * b.c1.y + 3 * mt * t2 * b.c2.y + t2 * t * b.end.y
  };
}

function canonicalLineAngle(angle) {
  let a = angle % Math.PI;
  if (a < 0) a += Math.PI;
  return a;
}

function lineNormalDistance(p, angle) {
  return p.x * (-Math.sin(angle)) + p.y * Math.cos(angle);
}

function lineAngleDiff(a, b) {
  let d = Math.abs(a - b) % Math.PI;
  if (d > Math.PI / 2) d = Math.PI - d;
  return Math.abs(d);
}

function intersectRayWithRect(pStart, u, rect) {
  let tMin = Infinity;
  if (u.x < -EPS) {
    const t = (rect.x - pStart.x) / u.x;
    if (t > 0) {
      const y = pStart.y + t * u.y;
      if (y >= rect.y - EPS && y <= rect.y + rect.height + EPS) tMin = Math.min(tMin, t);
    }
  }
  if (u.x > EPS) {
    const t = (rect.x + rect.width - pStart.x) / u.x;
    if (t > 0) {
      const y = pStart.y + t * u.y;
      if (y >= rect.y - EPS && y <= rect.y + rect.height + EPS) tMin = Math.min(tMin, t);
    }
  }
  if (u.y < -EPS) {
    const t = (rect.y - pStart.y) / u.y;
    if (t > 0) {
      const x = pStart.x + t * u.x;
      if (x >= rect.x - EPS && x <= rect.x + rect.width + EPS) tMin = Math.min(tMin, t);
    }
  }
  if (u.y > EPS) {
    const t = (rect.y + rect.height - pStart.y) / u.y;
    if (t > 0) {
      const x = pStart.x + t * u.x;
      if (x >= rect.x - EPS && x <= rect.x + rect.width + EPS) tMin = Math.min(tMin, t);
    }
  }

  if (isFinite(tMin) && tMin > 0) {
    return { x: pStart.x + tMin * u.x, y: pStart.y + tMin * u.y };
  }
  const reach = Math.max(rect.width, rect.height) * 1.5;
  return { x: pStart.x + u.x * reach, y: pStart.y + u.y * reach };
}

function extendLineToRect(line, rect) {
  if (!line || !line.p1 || !rect) return null;

  const angle = Number.isFinite(line.angle)
    ? line.angle
    : (line.p2 ? Math.atan2(line.p2.y - line.p1.y, line.p2.x - line.p1.x) : 0);
  const dx = Math.cos(angle);
  const dy = Math.sin(angle);
  const nx = -dy;
  const ny = dx;
  const offset = Number.isFinite(line.offset) ? line.offset : 0;

  // The normal offset is part of the line equation, not an ignored metadata field.
  const origin = {
    x: line.p1.x + nx * offset,
    y: line.p1.y + ny * offset
  };

  const x1 = Math.min(rect.x, rect.x + rect.width);
  const x2 = Math.max(rect.x, rect.x + rect.width);
  const y1 = Math.min(rect.y, rect.y + rect.height);
  const y2 = Math.max(rect.y, rect.y + rect.height);
  const tolerance = Math.max(EPS * 10, Math.max(x2 - x1, y2 - y1) * 1e-9);
  const hits = [];

  function addHit(x, y, t) {
    if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(t)) return;
    if (x < x1 - tolerance || x > x2 + tolerance || y < y1 - tolerance || y > y2 + tolerance) return;
    const point = { x: clamp(x, x1, x2), y: clamp(y, y1, y2), t };
    if (!hits.some(h => dist(h, point) <= tolerance * 4)) hits.push(point);
  }

  if (Math.abs(dx) > EPS) {
    let t = (x1 - origin.x) / dx;
    addHit(x1, origin.y + t * dy, t);
    t = (x2 - origin.x) / dx;
    addHit(x2, origin.y + t * dy, t);
  }
  if (Math.abs(dy) > EPS) {
    let t = (y1 - origin.y) / dy;
    addHit(origin.x + t * dx, y1, t);
    t = (y2 - origin.y) / dy;
    addHit(origin.x + t * dx, y2, t);
  }

  hits.sort((a, b) => a.t - b.t);
  if (hits.length >= 2) {
    return {
      p1: { x: hits[0].x, y: hits[0].y },
      p2: { x: hits[hits.length - 1].x, y: hits[hits.length - 1].y }
    };
  }

  // A line that does not cross the construction frame should not create a stray guide.
  return null;
}

function solveQuadratic(a, b, c) {
  // Normalisation évite que les très petites ou très grandes courbes changent
  // le résultat uniquement à cause de l'échelle des coordonnées.
  const scale = Math.max(Math.abs(a), Math.abs(b), Math.abs(c));
  if (!Number.isFinite(scale) || scale <= Number.EPSILON) return [];
  let A = a / scale, B = b / scale, C = c / scale;
  const coefficientTolerance = 1e-12;

  if (Math.abs(A) <= coefficientTolerance) {
    if (Math.abs(B) <= coefficientTolerance) return [];
    return [-C / B];
  }

  let discriminant = B * B - 4 * A * C;
  const discTolerance = 1e-14 * Math.max(1, B * B, Math.abs(4 * A * C));
  if (discriminant < -discTolerance) return [];
  if (Math.abs(discriminant) <= discTolerance) return [-B / (2 * A)];

  discriminant = Math.max(0, discriminant);
  const sqrtD = Math.sqrt(discriminant);
  const q = -0.5 * (B + (B >= 0 ? sqrtD : -sqrtD));
  if (Math.abs(q) <= coefficientTolerance) return [-B / (2 * A)];
  const r1 = q / A;
  const r2 = C / q;
  if (!Number.isFinite(r1) || !Number.isFinite(r2)) return [r1].filter(Number.isFinite);
  return Math.abs(r1 - r2) <= 1e-10 * Math.max(1, Math.abs(r1), Math.abs(r2))
    ? [(r1 + r2) * 0.5]
    : (r1 < r2 ? [r1, r2] : [r2, r1]);
}

function cubicExtremaParameters(b) {
  // B(t) = A t³ + 3B t² + 3C t + P0; solve A t² + 2B t + C = 0.
  const out = [];
  const ax = -b.start.x + 3 * b.c1.x - 3 * b.c2.x + b.end.x;
  const bx = b.start.x - 2 * b.c1.x + b.c2.x;
  const cx = b.c1.x - b.start.x;
  const ay = -b.start.y + 3 * b.c1.y - 3 * b.c2.y + b.end.y;
  const by = b.start.y - 2 * b.c1.y + b.c2.y;
  const cy = b.c1.y - b.start.y;
  solveQuadratic(ax, 2 * bx, cx).forEach(t => { if (t > EPS && t < 1 - EPS) out.push(t); });
  solveQuadratic(ay, 2 * by, cy).forEach(t => { if (t > EPS && t < 1 - EPS) out.push(t); });
  return out.sort((a, b) => a - b).filter((v, i, a) => a.every((x, j) => j === i || Math.abs(x - v) > 1e-7));
}

function cubicInflectionParameters(b) {
  const ax = -b.start.x + 3 * b.c1.x - 3 * b.c2.x + b.end.x;
  const ay = -b.start.y + 3 * b.c1.y - 3 * b.c2.y + b.end.y;
  const bx = b.start.x - 2 * b.c1.x + b.c2.x;
  const by = b.start.y - 2 * b.c1.y + b.c2.y;
  const cx = b.c1.x - b.start.x;
  const cy = b.c1.y - b.start.y;
  // B'(t) × B''(t) = 0. The common factor is irrelevant to the roots.
  const A = cross(ax, ay, bx, by);
  const B = cross(ax, ay, cx, cy);
  const C = cross(bx, by, cx, cy);
  return solveQuadratic(A, B, C).filter(t => t > EPS && t < 1 - EPS);
}

function cubicDerivative(b, t) {
  const mt = 1 - t;
  return {
    x: 3 * mt * mt * (b.c1.x - b.start.x) + 6 * mt * t * (b.c2.x - b.c1.x) + 3 * t * t * (b.end.x - b.c2.x),
    y: 3 * mt * mt * (b.c1.y - b.start.y) + 6 * mt * t * (b.c2.y - b.c1.y) + 3 * t * t * (b.end.y - b.c2.y)
  };
}

function cubicStationaryParameters(b) {
  // A stationary point inside a cubic segment occurs where both derivative
  // components vanish at the same parameter. Keep this separate from extrema:
  // a stationary cusp is a geometric landmark, not a native path anchor.
  const ax = -b.start.x + 3 * b.c1.x - 3 * b.c2.x + b.end.x;
  const bx = b.start.x - 2 * b.c1.x + b.c2.x;
  const cx = b.c1.x - b.start.x;
  const ay = -b.start.y + 3 * b.c1.y - 3 * b.c2.y + b.end.y;
  const by = b.start.y - 2 * b.c1.y + b.c2.y;
  const cy = b.c1.y - b.start.y;
  const rootsX = solveQuadratic(ax, 2 * bx, cx);
  const rootsY = solveQuadratic(ay, 2 * by, cy);
  const controlScale = Math.max(1, dist(b.start, b.c1), dist(b.c1, b.c2), dist(b.c2, b.end));
  const derivativeTolerance = Math.max(1e-10, controlScale * 1e-8);
  const parameterTolerance = 1e-5;
  const candidates = [];

  for (const tx of rootsX) {
    if (!(tx > EPS && tx < 1 - EPS)) continue;
    for (const ty of rootsY) {
      if (!(ty > EPS && ty < 1 - EPS) || Math.abs(tx - ty) > parameterTolerance) continue;
      const t = (tx + ty) * 0.5;
      const derivative = cubicDerivative(b, t);
      if (Math.hypot(derivative.x, derivative.y) > derivativeTolerance) continue;
      if (!candidates.some(value => Math.abs(value - t) <= parameterTolerance)) candidates.push(t);
    }
  }
  return candidates.sort((a, b) => a - b);
}

function classifyBezierStationaryPoint(b, t) {
  const available = Math.min(t, 1 - t);
  const delta = Math.max(1e-6, Math.min(1e-3, available * 0.2));
  const left = cubicDerivative(b, Math.max(0, t - delta));
  const right = cubicDerivative(b, Math.min(1, t + delta));
  const leftLength = Math.hypot(left.x, left.y);
  const rightLength = Math.hypot(right.x, right.y);
  if (leftLength <= 1e-12 || rightLength <= 1e-12) {
    return { type: "stationary", cusp: false, incomingTangent: null, outgoingTangent: null, turnAngle: 0 };
  }
  const incoming = { x: left.x / leftLength, y: left.y / leftLength };
  const outgoing = { x: right.x / rightLength, y: right.y / rightLength };
  const turn = Math.atan2(
    incoming.x * outgoing.y - incoming.y * outgoing.x,
    clamp(incoming.x * outgoing.x + incoming.y * outgoing.y, -1, 1)
  );
  const cusp = Math.abs(turn) >= 150 * DEG;
  return {
    type: cusp ? "cusp" : "stationary",
    cusp,
    incomingTangent: Math.atan2(incoming.y, incoming.x),
    outgoingTangent: Math.atan2(outgoing.y, outgoing.x),
    turnAngle: Math.abs(turn)
  };
}

function cubicSecondDerivative(b, t) {
  return {
    x: 6 * ((1 - t) * (b.c2.x - 2 * b.c1.x + b.start.x) + t * (b.end.x - 2 * b.c2.x + b.c1.x)),
    y: 6 * ((1 - t) * (b.c2.y - 2 * b.c1.y + b.start.y) + t * (b.end.y - 2 * b.c2.y + b.c1.y))
  };
}

function bezierEndpointTangent(b, atStart) {
  const chord = { x: b.end.x - b.start.x, y: b.end.y - b.start.y };
  const candidates = atStart
    ? [
        { x: b.c1.x - b.start.x, y: b.c1.y - b.start.y, source: "first-control" },
        { x: b.c2.x - b.start.x, y: b.c2.y - b.start.y, source: "second-control-fallback" },
        { x: chord.x, y: chord.y, source: "chord-fallback" }
      ]
    : [
        { x: b.end.x - b.c2.x, y: b.end.y - b.c2.y, source: "last-control" },
        { x: b.end.x - b.c1.x, y: b.end.y - b.c1.y, source: "first-control-fallback" },
        { x: chord.x, y: chord.y, source: "chord-fallback" }
      ];
  const scale = Math.max(1, ...candidates.map(v => Math.hypot(v.x, v.y)));
  const threshold = Math.max(1e-10, scale * 1e-9);
  for (const v of candidates) {
    const length = Math.hypot(v.x, v.y);
    if (length <= threshold) continue;
    const x = v.x / length, y = v.y / length;
    return { x, y, length, angle: Math.atan2(y, x), source: v.source };
  }
  return { x: 0, y: 0, length: 0, angle: 0, source: "degenerate" };
}

function bezierCurvatureAt(b, t) {
  const d = cubicDerivative(b, t);
  const dd = cubicSecondDerivative(b, t);
  const speed = Math.hypot(d.x, d.y);
  const controlScale = Math.max(1, dist(b.start, b.c1), dist(b.c1, b.c2), dist(b.c2, b.end));
  if (speed <= Math.max(1e-10, controlScale * 1e-9)) return 0;
  const curvature = cross(d.x, d.y, dd.x, dd.y) / Math.pow(speed, 3);
  return Number.isFinite(curvature) ? curvature : 0;
}

function curveClosureTolerance(beziers) {
  if (!beziers || !beziers.length) return 1e-5;
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const b of beziers) {
    const points = [b.start, b.c1, b.c2, b.end];
    for (const p of points) {
      if (!p || !Number.isFinite(p.x) || !Number.isFinite(p.y)) continue;
      minX = Math.min(minX, p.x);
      minY = Math.min(minY, p.y);
      maxX = Math.max(maxX, p.x);
      maxY = Math.max(maxY, p.y);
    }
  }
  const diagonal = Number.isFinite(minX) && Number.isFinite(minY) && Number.isFinite(maxX) && Number.isFinite(maxY)
    ? Math.max(1, Math.hypot(maxX - minX, maxY - minY))
    : 1;
  return Math.max(1e-5, Math.min(0.05, diagonal * 1e-6));
}

function isCurveClosed(curve, beziers) {
  let explicitlyClosed = false;
  try {
    const value = curve.isClosed;
    explicitlyClosed = typeof value === "function" ? !!value.call(curve) : value === true;
  } catch (e) {}
  if (explicitlyClosed) return true;
  if (!beziers || !beziers.length) return false;

  const first = beziers[0].start;
  const last = beziers[beziers.length - 1].end;
  // Even if the API reports isClosed=false, coincident start/end geometry is
  // topologically closed. A declared true flag also covers implicit close edges.
  return dist(first, last) <= curveClosureTolerance(beziers);
}

function calculateNearestDistances(points, searchRadius) {
  const cellSize = Math.max(0.25, searchRadius || 1);
  const buckets = new Map();
  const keys = points.map(p => ({ x: Math.floor(p.x / cellSize), y: Math.floor(p.y / cellSize) }));
  for (let i = 0; i < points.length; i++) {
    const key = keys[i];
    const bucketKey = key.x + "," + key.y;
    if (!buckets.has(bucketKey)) buckets.set(bucketKey, []);
    buckets.get(bucketKey).push(i);
  }
  const result = new Array(points.length).fill(Infinity);
  for (let i = 0; i < points.length; i++) {
    const key = keys[i];
    let nearest = Infinity;
    for (let dx = -1; dx <= 1; dx++) {
      for (let dy = -1; dy <= 1; dy++) {
        const bucket = buckets.get((key.x + dx) + "," + (key.y + dy));
        if (!bucket) continue;
        for (const j of bucket) {
          if (i === j) continue;
          const d = dist(points[i], points[j]);
          if (d < nearest) nearest = d;
        }
      }
    }
    result[i] = nearest;
  }
  return result;
}

function fitCircleToBezier(b) {
  const chord = dist(b.start, b.end);
  const controlSpan = Math.max(dist(b.start, b.c1), dist(b.c1, b.c2), dist(b.c2, b.end));
  const closedCubic = chord <= Math.max(1e-8, controlSpan * 1e-6);
  if (!closedCubic && chord < 1.0) return null;
  if (closedCubic && controlSpan < 2.5) return null;

  if (!closedCubic) {
    const dx = b.end.x - b.start.x, dy = b.end.y - b.start.y;
    const invChord = 1.0 / chord;
    const h1 = Math.abs(cross(dx, dy, b.c1.x - b.start.x, b.c1.y - b.start.y)) * invChord;
    const h2 = Math.abs(cross(dx, dy, b.c2.x - b.start.x, b.c2.y - b.start.y)) * invChord;
    if (h1 < 0.45 && h2 < 0.45) return null;
  }

  const N = 7;
  const pts = [];
  let sumX = 0, sumY = 0;
  for (let i = 0; i < N; i++) {
    const t = i / (N - 1);
    const p = cubicPoint(b, t);
    pts.push(p);
    sumX += p.x; sumY += p.y;
  }
  const mx = sumX / N, my = sumY / N;

  let Suu = 0, Svv = 0, Suv = 0;
  let Suuu = 0, Svvv = 0, Suvv = 0, Svuu = 0;
  for (let i = 0; i < N; i++) {
    const u = pts[i].x - mx, v = pts[i].y - my;
    const u2 = u * u, v2 = v * v;
    Suu += u2; Svv += v2; Suv += u * v;
    Suuu += u2 * u; Svvv += v2 * v;
    Suvv += u * v2; Svuu += v * u2;
  }

  const det = Suu * Svv - Suv * Suv;
  if (Math.abs(det) < 1e-4) return null;

  const rhs1 = 0.5 * (Suuu + Suvv);
  const rhs2 = 0.5 * (Svvv + Svuu);
  const uc = (rhs1 * Svv - rhs2 * Suv) / det;
  const vc = (Suu * rhs2 - Suv * rhs1) / det;
  const cx = uc + mx, cy = vc + my;
  const r = Math.sqrt(uc * uc + vc * vc + (Suu + Svv) / N);

  if (!isFinite(r) || r < 2.5 || r > 8000.0) return null;

  let maxDev = 0;
  for (let i = 0; i < N; i++) {
    const d = Math.abs(dist(pts[i], { x: cx, y: cy }) - r);
    if (d > maxDev) maxDev = d;
  }
  const allowedDev = Math.max(0.65, r * 0.022);
  if (maxDev > allowedDev) return null;

  return { cx, cy, r, confidence: 1 - (maxDev / allowedDev) };
}

function buildAnchorTopology(records, mergeTolerance) {
  const anchors = [];
  const requestedTolerance = Number(mergeTolerance);
  const cellSize = Math.max(1e-8, Number.isFinite(requestedTolerance) && requestedTolerance > 0 ? requestedTolerance : 1e-5);
  const buckets = new Map();
  const topologyKeys = new Map();

  function bucketKey(x, y) { return x + "," + y; }
  function addUniqueVector(list, vector) {
    if (!vector || !Number.isFinite(vector.x) || !Number.isFinite(vector.y)) return;
    const length = Math.hypot(vector.x, vector.y);
    if (length <= 1e-10) return;
    const normalized = { x: vector.x / length, y: vector.y / length };
    if (!list.some(v => Math.hypot(v.x - normalized.x, v.y - normalized.y) < 1e-7)) list.push(normalized);
  }
  function createAnchor(point, record) {
    const anchor = {
      x: point.x,
      y: point.y,
      incoming: [],
      outgoing: [],
      incomingVectors: [],
      outgoingVectors: [],
      curvatureValues: [],
      endpoint: false,
      closedContour: false,
      corner: false,
      cusp: false,
      extrema: false,
      inflection: false,
      importance: 30,
      sourceContours: [],
      sourceSegments: [],
      topologyKey: record && record.topologyKey !== undefined ? record.topologyKey : null,
      coordinateDriftMax: 0
    };
    anchors.push(anchor);
    return anchor;
  }

  for (const r of records) {
    if (!r || !r.point || !Number.isFinite(r.point.x) || !Number.isFinite(r.point.y)) continue;
    let anchor = null;

    // Native vertex identity wins over coordinate proximity. Adjacent Bézier
    // segments share a topologyKey; distinct nodes on a tight curve, a cusp or
    // a self-intersection keep their own identity even when coordinates are
    // almost coincident. This also removes the need for one global tolerance
    // to solve every contour's closed seam.
    if (r.topologyKey !== undefined && r.topologyKey !== null) {
      const key = String(r.topologyKey);
      anchor = topologyKeys.get(key) || null;
      if (!anchor) {
        anchor = createAnchor(r.point, r);
        topologyKeys.set(key, anchor);
      }
    } else {
      // Compatibility fallback for callers that supply only point records.
      const gx = Math.floor(r.point.x / cellSize);
      const gy = Math.floor(r.point.y / cellSize);
      let bestDistance = Infinity;
      for (let dx = -1; dx <= 1; dx++) {
        for (let dy = -1; dy <= 1; dy++) {
          const bucket = buckets.get(bucketKey(gx + dx, gy + dy));
          if (!bucket) continue;
          for (const index of bucket) {
            const candidate = anchors[index];
            const d = dist(candidate, r.point);
            if (d <= cellSize && d < bestDistance) {
              anchor = candidate;
              bestDistance = d;
            }
          }
        }
      }
      if (!anchor) {
        anchor = createAnchor(r.point, r);
        const index = anchors.length - 1;
        const key = bucketKey(gx, gy);
        if (!buckets.has(key)) buckets.set(key, []);
        buckets.get(key).push(index);
      }
    }

    anchor.coordinateDriftMax = Math.max(anchor.coordinateDriftMax || 0, dist(anchor, r.point));
    if (r.incoming !== null && Number.isFinite(r.incoming)) anchor.incoming.push(r.incoming);
    if (r.outgoing !== null && Number.isFinite(r.outgoing)) anchor.outgoing.push(r.outgoing);
    addUniqueVector(anchor.incomingVectors, r.incomingVector);
    addUniqueVector(anchor.outgoingVectors, r.outgoingVector);
    if (Number.isFinite(r.incomingCurvature)) anchor.curvatureValues.push({
      value: Math.abs(r.incomingCurvature),
      scale: Math.max(0, Number(r.incomingCurvatureScale) || 0)
    });
    if (Number.isFinite(r.outgoingCurvature)) anchor.curvatureValues.push({
      value: Math.abs(r.outgoingCurvature),
      scale: Math.max(0, Number(r.outgoingCurvatureScale) || 0)
    });
    anchor.endpoint = anchor.endpoint || !!r.endpoint;
    anchor.closedContour = anchor.closedContour || !!r.closedContour;
    if (Number.isInteger(r.contourIndex) && anchor.sourceContours.indexOf(r.contourIndex) < 0) anchor.sourceContours.push(r.contourIndex);
    if (Number.isInteger(r.segmentIndex)) anchor.sourceSegments.push({ contour: r.contourIndex, segment: r.segmentIndex });
  }
  return anchors;
}

function detectDominantDirection(segments) {
  const bins = 36, weights = new Array(bins).fill(0);
  for (const s of segments) {
    const len = dist(s.p1, s.p2);
    if (len < 0.5) continue;
    const angle = canonicalLineAngle(Math.atan2(s.p2.y - s.p1.y, s.p2.x - s.p1.x));
    const idx = Math.round(angle / Math.PI * bins) % bins;
    weights[idx] += len;
  }
  let best = 0;
  for (let i = 1; i < bins; i++) if (weights[i] > weights[best]) best = i;
  return (best / bins) * Math.PI;
}

function detectAxisSymmetry(anchors, angle) {
  if (anchors.length < 3) return { score: 0, axis: angle, perpendicular: angle + Math.PI / 2 };
  const ca = Math.cos(angle), sa = Math.sin(angle);
  const points = anchors.map(p => ({ u: p.x * ca + p.y * sa, v: -p.x * sa + p.y * ca }));
  const uMin = Math.min.apply(null, points.map(p => p.u)), uMax = Math.max.apply(null, points.map(p => p.u));
  const vMin = Math.min.apply(null, points.map(p => p.v)), vMax = Math.max.apply(null, points.map(p => p.v));
  const uMid = (uMin + uMax) / 2, vMid = (vMin + vMax) / 2;
  const scale = Math.max(1, Math.min(uMax - uMin, vMax - vMin));

  function mirrorScore(useU) {
    let matched = 0;
    for (const p of points) {
      const target = useU ? { u: 2 * uMid - p.u, v: p.v } : { u: p.u, v: 2 * vMid - p.v };
      let best = Infinity;
      for (const q of points) best = Math.min(best, Math.hypot(target.u - q.u, target.v - q.v));
      if (best <= Math.max(2.0, scale * 0.03)) matched++;
    }
    return matched / points.length;
  }
  const longitudinal = mirrorScore(false), transverse = mirrorScore(true);
  return {
    longitudinal: longitudinal,
    transverse: transverse,
    score: Math.max(longitudinal, transverse),
    axis: longitudinal >= transverse ? angle : angle + Math.PI / 2,
    perpendicular: longitudinal >= transverse ? angle + Math.PI / 2 : angle
  };
}

function detectRepeatedModules(anchors, bounds) {
  // Compatibility placeholder. The previous all-pairs distance histogram was
  // quadratic and is superseded by detectModularSystems(), which runs after the
  // protected geometry analysis using projected consecutive intervals.
  return { module: 0, ratios: [], confidence: 0, axes: [] };
}

function featureImportanceForAnchor(a) {
  let score = 30;
  if (a.endpoint) score += 20;
  if (a.corner) score += 55;
  if (a.cusp) score += 24;
  if (a.extrema) score += 20;
  if (a.inflection) score += 8;
  score += Math.min(24, Number(a.curvatureImportance) || 0);
  return Math.min(100, score);
}

// Analisador geométrico universal de alta fidelidade
function analyzeSmartGeometry(polyCurve, baseAnchorSize, baseHandleSize) {
  const rawHandles = [], straightSegments = [], directionSegments = [], rawCircles = [], landmarkRecords = [], topologyRecords = [];
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  let realCurveSegments = 0;

  function updateBounds(p) {
    minX = Math.min(minX, p.x); minY = Math.min(minY, p.y);
    maxX = Math.max(maxX, p.x); maxY = Math.max(maxY, p.y);
  }

  const closedPetals = [];
  let closedContourTotal = 0;

  for (let c = 0; c < polyCurve.curveCount; c++) {
    const curve = polyCurve.at(c);
    const beziers = collectBeziers(curve);
    const closedContour = isCurveClosed(curve, beziers);
    if (closedContour) closedContourTotal++;
    const firstContourPoint = beziers.length ? beziers[0].start : null;
    const lastContourPoint = beziers.length ? beziers[beziers.length - 1].end : null;
    const contourSeamLength = firstContourPoint && lastContourPoint ? dist(firstContourPoint, lastContourPoint) : Infinity;
    const contourSeamTolerance = curveClosureTolerance(beziers);
    const hasImplicitClosingEdge = closedContour && contourSeamLength > contourSeamTolerance;
    const contourPoints = [];
    const contourEdges = [];
    let contourScale = 1;

    for (let bIdx = 0; bIdx < beziers.length; bIdx++) {
      const b = beziers[bIdx];
      updateBounds(b.start); updateBounds(b.end);
      contourPoints.push(b.start);

      const chord = dist(b.start, b.end);
      const dC1 = dist(b.start, b.c1), dC2 = dist(b.end, b.c2);
      const d12 = dist(b.c1, b.c2);
      const dx = b.end.x - b.start.x, dy = b.end.y - b.start.y;
      const controlScale = Math.max(chord, dC1, dC2, d12, 1e-8);
      contourScale = Math.max(contourScale, controlScale);
      const endVertexIndex = (closedContour && bIdx === beziers.length - 1 && !hasImplicitClosingEdge)
        ? 0
        : bIdx + 1;
      const referenceVectors = [
        { x: dx, y: dy },
        { x: b.c1.x - b.start.x, y: b.c1.y - b.start.y },
        { x: b.c2.x - b.start.x, y: b.c2.y - b.start.y }
      ];
      let reference = referenceVectors[0];
      for (const v of referenceVectors) if (Math.hypot(v.x, v.y) > Math.hypot(reference.x, reference.y)) reference = v;
      const referenceLength = Math.hypot(reference.x, reference.y);
      // Keep the straightness test scale-relative. An absolute 0.45-unit floor
      // misclassified genuinely curved small marks (including tight cusp details)
      // as lines. The cap only suppresses sub-quarter-unit numerical noise on
      // very large document-space paths.
      const straightTolerance = Math.max(1e-5, Math.min(0.25, controlScale * 1e-4));
      const h1 = referenceLength > 1e-10
        ? Math.abs(cross(reference.x, reference.y, b.c1.x - b.start.x, b.c1.y - b.start.y)) / referenceLength
        : Infinity;
      const h2 = referenceLength > 1e-10
        ? Math.abs(cross(reference.x, reference.y, b.c2.x - b.start.x, b.c2.y - b.start.y)) / referenceLength
        : Infinity;
      // A closed cubic can have a zero chord but still describe a loop. Use
      // the longest control-polygon direction instead of treating its zero
      // chord as proof that the segment is straight.
      const isSegmentStraight = referenceLength > 1e-10 && h1 < straightTolerance && h2 < straightTolerance;

      if (isSegmentStraight) {
        if (chord >= 1.0) {
          const angle = canonicalLineAngle(Math.atan2(b.end.y - b.start.y, b.end.x - b.start.x));
          const seg = { p1: b.start, p2: b.end, angle: angle, length: chord, importance: 85 };
          straightSegments.push(seg);
          directionSegments.push({ p1: b.start, p2: b.end });
          contourEdges.push(seg);
        }
      } else {
        realCurveSegments++;
        const circ = fitCircleToBezier(b);
        if (circ) rawCircles.push(circ);
        const mid = cubicPoint(b, 0.5);
        directionSegments.push({ p1: b.start, p2: mid });
        directionSegments.push({ p1: mid, p2: b.end });

        const handleEpsilon = Math.max(1e-9, controlScale * 1e-9);
        if (dC1 > handleEpsilon) {
          rawHandles.push({
            anchor: b.start, handle: b.c1, length: dC1,
            importance: Math.min(100, 35 + dC1 * 0.5),
            contourIndex: c, segmentIndex: bIdx, controlSide: "outgoing",
            anchorTopologyKey: c + ":vertex:" + bIdx,
            closedContour
          });
        }
        if (dC2 > handleEpsilon) {
          rawHandles.push({
            anchor: b.end, handle: b.c2, length: dC2,
            importance: Math.min(100, 35 + dC2 * 0.5),
            contourIndex: c, segmentIndex: bIdx, controlSide: "incoming",
            anchorTopologyKey: c + ":vertex:" + endVertexIndex,
            closedContour
          });
        }

        // Exact derivative roots are shared by the outline bounds, curvature
        // landmarks and anchor classification. No uniform sampling is used to
        // invent or move anchor nodes.
        const extremaT = cubicExtremaParameters(b);
        extremaT.forEach(t => {
          const p = cubicPoint(b, t);
          const d = cubicDerivative(b, t);
          landmarkRecords.push({
            x: p.x, y: p.y, type: "extrema", importance: 70,
            contourIndex: c, segmentIndex: bIdx, t,
            tangentAngle: Math.atan2(d.y, d.x),
            curvature: bezierCurvatureAt(b, t)
          });
          updateBounds(p);
        });

        const inflectionT = cubicInflectionParameters(b);
        inflectionT.forEach(t => {
          const p = cubicPoint(b, t);
          const d = cubicDerivative(b, t);
          landmarkRecords.push({
            x: p.x, y: p.y, type: "inflection", importance: 45,
            contourIndex: c, segmentIndex: bIdx, t,
            tangentAngle: Math.atan2(d.y, d.x),
            curvature: 0
          });
          updateBounds(p);
        });

        // A cubic may contain a cusp even when its control points have no native
        // anchor at that location. Detect it from simultaneous derivative roots.
        // Merge with an already detected extremum/inflection at the same t rather
        // than drawing duplicate markers over one geometric singularity.
        const stationaryT = cubicStationaryParameters(b);
        stationaryT.forEach(t => {
          const classification = classifyBezierStationaryPoint(b, t);
          const p = cubicPoint(b, t);
          const existing = landmarkRecords.find(l =>
            l.contourIndex === c && l.segmentIndex === bIdx && Number.isFinite(l.t) && Math.abs(l.t - t) <= 1e-5
          );
          if (existing) {
            if (classification.cusp) {
              existing.type = "cusp";
              existing.importance = 96;
              existing.cusp = true;
              existing.turnAngle = classification.turnAngle;
              existing.incomingTangent = classification.incomingTangent;
              existing.outgoingTangent = classification.outgoingTangent;
            } else {
              existing.stationary = true;
            }
          } else {
            landmarkRecords.push({
              x: p.x, y: p.y,
              type: classification.type,
              importance: classification.cusp ? 96 : 58,              cusp: classification.cusp,
              stationary: true,
              turnAngle: classification.turnAngle,
              incomingTangent: classification.incomingTangent,
              outgoingTangent: classification.outgoingTangent,
              contourIndex: c, segmentIndex: bIdx, t,
              curvature: bezierCurvatureAt(b, t)
            });
          }
          updateBounds(p);
        });
      }

      const startTangent = bezierEndpointTangent(b, true);
      const endTangent = bezierEndpointTangent(b, false);
      const startCurvature = bezierCurvatureAt(b, 0);
      const endCurvature = bezierCurvatureAt(b, 1);

      topologyRecords.push({
        point: b.start,
        incoming: null,
        outgoing: startTangent.length > 0 ? startTangent.angle : null,
        outgoingVector: startTangent,
        outgoingCurvature: startCurvature,
        outgoingCurvatureScale: Math.max(chord, dC1, 1e-8),
        endpoint: !closedContour && bIdx === 0,
        closedContour,
        contourIndex: c,
        segmentIndex: bIdx,
        topologyKey: c + ":vertex:" + bIdx
      });
      topologyRecords.push({
        point: b.end,
        incoming: endTangent.length > 0 ? endTangent.angle : null,
        incomingVector: endTangent,
        incomingCurvature: endCurvature,
        incomingCurvatureScale: Math.max(chord, dC2, 1e-8),
        outgoing: null,
        endpoint: !closedContour && bIdx === beziers.length - 1,
        closedContour,
        contourIndex: c,
        segmentIndex: bIdx,
        topologyKey: c + ":vertex:" + endVertexIndex
      });
    }

    // Some document APIs report a closed path while exposing its closing edge
    // implicitly: the final Bézier endpoint is then different from the first
    // Bézier start. Add that straight closure to the topology so both seam
    // vertices receive their missing incoming/outgoing direction. Do not add
    // anything when the final endpoint already meets the first start.
    if (closedContour && beziers.length > 0) {
      const first = beziers[0].start;
      const last = beziers[beziers.length - 1].end;
      const seamDx = first.x - last.x;
      const seamDy = first.y - last.y;
      const seamLength = Math.hypot(seamDx, seamDy);
      const seamTolerance = curveClosureTolerance(beziers);

      if (seamLength > seamTolerance) {
        // The final endpoint is a real vertex of the implicit closing edge.
        // Include it in the closed-contour polygonal analysis.
        contourPoints.push(last);
        const seamVector = { x: seamDx / seamLength, y: seamDy / seamLength };
        const seamAngle = Math.atan2(seamVector.y, seamVector.x);
        const lastIndex = beziers.length - 1;

        topologyRecords.push({
          point: last,
          incoming: null,
          outgoing: seamAngle,
          outgoingVector: seamVector,
          outgoingCurvature: 0,
          outgoingCurvatureScale: seamLength,
          endpoint: false,
          closedContour: true,
          contourIndex: c,
          segmentIndex: beziers.length,
          topologyKey: c + ":vertex:" + beziers.length
        });
        topologyRecords.push({
          point: first,
          incoming: seamAngle,
          incomingVector: seamVector,
          incomingCurvature: 0,
          incomingCurvatureScale: seamLength,
          outgoing: null,
          endpoint: false,
          closedContour: true,
          contourIndex: c,
          segmentIndex: -1,
          topologyKey: c + ":vertex:0"
        });

        // The implicit closing edge also contributes to direction analysis
        // and to polygonal/radial construction, but very short closures are
        // not promoted to visible straight-edge guides.
        if (seamLength >= 0.5) directionSegments.push({ p1: last, p2: first });
        if (seamLength >= 1.0) {
          const closure = {
            p1: last,
            p2: first,
            angle: canonicalLineAngle(seamAngle),
            length: seamLength,
            importance: 85,
            implicitClosure: true
          };
          straightSegments.push(closure);
          contourEdges.push(closure);
        }
      }
    }

    // Only truly closed contours feed the radial-petal analyser. Open paths
    // with three or more segments must not be mistaken for closed petals.
    if (closedContour && contourPoints.length >= 3) {
      closedPetals.push({ pts: contourPoints, edges: contourEdges });
    }
  }

  const geometryScale = Math.max(1, Math.hypot(maxX - minX, maxY - minY));
  // Native vertex keys now define all path topology. This small fallback
  // tolerance applies only to external records without a topologyKey.
  const anchorMergeTolerance = Math.max(1e-8, Math.min(1e-4, geometryScale * 1e-9));
  const topology = buildAnchorTopology(topologyRecords, anchorMergeTolerance);
  // Native vertices are never merged merely because they are spatially close.
  const uniqueAnchors = topology.slice();

  const bounds = {
    x: isFinite(minX) ? minX : 0, y: isFinite(minY) ? minY : 0,
    width: isFinite(maxX - minX) ? maxX - minX : 100,
    height: isFinite(maxY - minY) ? maxY - minY : 100
  };
  const center = { x: bounds.x + bounds.width / 2, y: bounds.y + bounds.height / 2 };

  // Identificação topológica de pétalas e cortes (caso existam formas poligonais)
  const petalData = [];
  for (const cp of closedPetals) {
    const dists = cp.pts.map(p => ({ p, d: dist(p, center) }));
    dists.sort((a, b) => a.d - b.d);
    const rIn = dists[0].d;
    const rOut = dists[dists.length - 1].d;
    const rMid = (rIn + rOut) * 0.5;

    const sortedEdges = cp.edges.slice().sort((e1, e2) => e2.length - e1.length);
    const radialEdges = [];
    const capEdges = [];

    // As 2 arestas mais longas são radiais
    for (const e of sortedEdges.slice(0, 2)) {
      const d1 = dist(e.p1, center);
      const d2 = dist(e.p2, center);
      const pIn = (d1 <= d2) ? e.p1 : e.p2;
      const pOut = (d1 <= d2) ? e.p2 : e.p1;
      const len = dist(pIn, pOut);
      if (len < 1.0) continue;
      const ux = (pOut.x - pIn.x) / len;
      const uy = (pOut.y - pIn.y) / len;
      radialEdges.push({ pIn, pOut, len, dir: { x: ux, y: uy }, angle: canonicalLineAngle(Math.atan2(uy, ux)) });
    }

    // As 2 arestas curtas de fecho são transversais (cortes das pontas)
    for (const e of sortedEdges.slice(2, 4)) {
      const len = dist(e.p1, e.p2);
      if (len < 1.0) continue;
      const tx = (e.p2.x - e.p1.x) / len;
      const ty = (e.p2.y - e.p1.y) / len;
      capEdges.push({ p1: e.p1, p2: e.p2, len, dir: { x: tx, y: ty }, angle: canonicalLineAngle(Math.atan2(ty, tx)) });
    }

    petalData.push({ pts: cp.pts, rIn, rOut, rMid, radialEdges, capEdges });
  }

  // =========================================================================
  // CRITÉRIO RIGOROSO DE ARQUITETURA RADIAL (EVITA FALSOS POSITIVOS EM LOGOS QUADRADOS)
  // =========================================================================
  // Mede a diversidade de ângulos radiais
  const uniqueRayAngles = [];
  for (const p of petalData) {
    for (const e of p.radialEdges) {
      if (!uniqueRayAngles.some(a => lineAngleDiff(a, e.angle) < 8.0 * DEG)) {
        uniqueRayAngles.push(e.angle);
      }
    }
  }

  // Círculos de Bézier analíticos
  const uniqueCircles = [];
  for (const c of rawCircles) {
    const match = uniqueCircles.find(ex => dist(ex, c) < Math.max(3.0, c.r * 0.04) && Math.abs(ex.r - c.r) < Math.max(2.5, c.r * 0.035));
    if (!match) {
      uniqueCircles.push({ cx: c.cx, cy: c.cy, r: c.r, confidence: c.confidence });
    }
  }

  let innerBand = [];
  let outerBand = [];

  // Para ser genuinamente um arranjo radial precisa de >= 6 ângulos distintos em 360° E pelo menos 8 pétalas
  const isRadialArray = (petalData.length >= 8 && uniqueRayAngles.length >= 6);

  if (isRadialArray) {
    petalData.sort((a, b) => a.rMid - b.rMid);
    let maxGap = 0, splitIdx = -1;
    for (let i = 0; i < petalData.length - 1; i++) {
      const g = petalData[i + 1].rMid - petalData[i].rMid;
      if (g > maxGap && g > 15.0) { maxGap = g; splitIdx = i; }
    }
    if (splitIdx >= 0) {
      innerBand = petalData.slice(0, splitIdx + 1);
      outerBand = petalData.slice(splitIdx + 1);
    } else {
      innerBand = petalData;
    }

    // Se não tiver círculos de Bézier, verifica se os anéis poligonais têm fidelidade circular estrita (< 2.5% variância)
    if (uniqueCircles.length === 0) {
      function testCircularity(radii) {
        if (!radii || radii.length < 6) return null;
        const meanR = radii.reduce((s, r) => s + r, 0) / radii.length;
        const variance = radii.reduce((s, r) => s + Math.pow(r - meanR, 2), 0) / radii.length;
        if ((Math.sqrt(variance) / meanR) > 0.025) return null;
        return meanR;
      }
      const r1 = testCircularity(innerBand.map(p => p.rIn));
      const r2 = testCircularity(innerBand.map(p => p.rOut));
      const r3 = outerBand.length ? testCircularity(outerBand.map(p => p.rIn)) : null;
      const r4 = outerBand.length ? testCircularity(outerBand.map(p => p.rOut)) : null;
      [r1, r2, r3, r4].filter(Boolean).forEach(r => uniqueCircles.push({ cx: center.x, cy: center.y, r }));
    }
  }

  for (const a of topology) {
    let maxTurn = 0;
    let minTurn = Infinity;
    for (const incoming of a.incomingVectors) {
      for (const outgoing of a.outgoingVectors) {
        const dot = clamp(incoming.x * outgoing.x + incoming.y * outgoing.y, -1, 1);
        const signedTurn = Math.atan2(
          incoming.x * outgoing.y - incoming.y * outgoing.x,
          dot
        );
        const turn = Math.abs(signedTurn);
        maxTurn = Math.max(maxTurn, turn);
        minTurn = Math.min(minTurn, turn);
      }
    }
    const maxCurvature = a.curvatureValues.length
      ? Math.max.apply(null, a.curvatureValues.map(v => v.value))
      : 0;
    const maxLocalBend = a.curvatureValues.length
      ? Math.max.apply(null, a.curvatureValues.map(v => v.value * v.scale))
      : 0;
    a.turnAngle = maxTurn;
    a.turnAngleDegrees = maxTurn / DEG;
    a.cusp = maxTurn >= 150 * DEG;
    a.corner = maxTurn >= 26 * DEG;
    a.smoothJoin = Number.isFinite(minTurn) && maxTurn < 8 * DEG;
    a.curvature = maxCurvature;
    // Local curvature multiplied by adjacent segment scale distinguishes a
    // compact, meaningful bend from harmless numerical curvature. This is
    // scale-independent and protects important nodes on tight Bezier sections.
    a.localBend = maxLocalBend;
    a.curvatureImportance = clamp(maxLocalBend * 28, 0, 24);
    a.junctionType = a.endpoint ? "endpoint" : (a.cusp ? "cusp" : (a.corner ? "corner" : (a.smoothJoin ? "smooth" : "junction")));
    a.importance = featureImportanceForAnchor(a);
  }

  const dominantAngle = detectDominantDirection(directionSegments);
  const symmetry = detectAxisSymmetry(uniqueAnchors, dominantAngle);
  const modules = detectRepeatedModules(uniqueAnchors, bounds);
  const sortedAnchors = uniqueAnchors.slice().sort((a, b) => b.importance - a.importance);

  const baseHalf = baseAnchorSize / 2;
  const nearestAnchorDistances = calculateNearestDistances(sortedAnchors, Math.max(1, baseAnchorSize * 2.4));
  const adaptiveAnchors = sortedAnchors.map((a, i) => {
    const nearest = nearestAnchorDistances[i];
    const halfSize = nearest < baseAnchorSize * 2.4 ? Math.max(1.0, Math.min(baseHalf, nearest * 0.32)) : baseHalf;
    return Object.assign({}, a, { halfSize: halfSize, clearance: nearest, priority: a.importance });
  });

  const adaptiveHandles = [];
  const baseDotR = baseHandleSize / 2;
  const handleMinLength = Math.max(1e-9, geometryScale * 1e-9);
  for (const h of rawHandles) {
    const parent = adaptiveAnchors.find(a => h.anchorTopologyKey !== undefined && a.topologyKey === h.anchorTopologyKey) ||
      adaptiveAnchors.find(a => dist(a, h.anchor) <= anchorMergeTolerance * 1.5);
    if (!parent || h.length <= handleMinLength) continue;
    let nearestOther = Infinity;
    for (const a of adaptiveAnchors) if (a !== parent) nearestOther = Math.min(nearestOther, dist(h.handle, a));
    for (const other of rawHandles) if (other !== h) nearestOther = Math.min(nearestOther, dist(h.handle, other.handle));
    const localClearance = Math.min(nearestOther, dist(h.handle, parent));
    // Amortecimento mais forte em áreas densas. A filtragem visual posterior
    // decide se um marcador deve ser ocultado quando nem o tamanho mínimo cabe.
    const minDotR = Math.max(0.8, Math.min(1.2, baseDotR * 0.25));
    const calculatedDotR = localClearance < baseHandleSize * 2.2
      ? Math.max(minDotR, Math.min(baseDotR, localClearance * 0.22))
      : baseDotR;

    adaptiveHandles.push({
      anchor: h.anchor,
      handle: h.handle,
      dotRadius: calculatedDotR,
      baseLength: h.length,
      importance: h.importance,
      clearance: localClearance,
      priority: h.importance
    });
  }

  return {
    anchors: adaptiveAnchors,
    handles: adaptiveHandles,
    straightSegments: straightSegments,
    petalData: petalData,
    innerBand: innerBand,
    outerBand: outerBand,
    circles: uniqueCircles,
    dominantAngle: dominantAngle,
    bounds: bounds,
    center: center,
    hasRealCurves: realCurveSegments > 0,
    isRadialArray: isRadialArray,
    symmetry: symmetry,
    modules: modules,
    landmarks: landmarkRecords,
    anchorMergeTolerance: anchorMergeTolerance,
    closedContourCount: closedContourTotal,
    radialPetalCandidateCount: closedPetals.length,
    featureCount: adaptiveAnchors.length + adaptiveHandles.length + uniqueCircles.length
  };
}

function lineSignedNormalOffset(line, angle) {
  const nx = -Math.sin(angle);
  const ny = Math.cos(angle);
  const explicitOffset = Number.isFinite(line.offset) ? line.offset : 0;
  return line.p1.x * nx + line.p1.y * ny + explicitOffset;
}

function filterUniqueLines(rawLines, mergeDist, referenceBounds) {
  const result = [];
  const span = referenceBounds
    ? Math.max(1, Math.hypot(referenceBounds.width, referenceBounds.height))
    : 1000;
  const positionTolerance = Math.max(0.5, Number(mergeDist) || 1);
  // Angular tolerance tightens for large marks, so slightly different diagonals
  // are not collapsed just because they are close near the origin.
  const angleTolerance = Math.max(0.06 * DEG, Math.min(0.45 * DEG, Math.atan2(positionTolerance * 0.35, span)));
  const sorted = rawLines.slice().sort((a, b) => {
    const scoreA = (a.importance || 0) + Math.min(20, (a.support || 0) * 2);
    const scoreB = (b.importance || 0) + Math.min(20, (b.support || 0) * 2);
    return scoreB - scoreA;
  }).slice(0, 1200);

  for (const l of sorted) {
    if (!l || !l.p1 || !Number.isFinite(l.p1.x) || !Number.isFinite(l.p1.y)) continue;
    let angle = l.angle;
    if (!Number.isFinite(angle)) {
      if (!l.p2 || !Number.isFinite(l.p2.x) || !Number.isFinite(l.p2.y)) continue;
      angle = Math.atan2(l.p2.y - l.p1.y, l.p2.x - l.p1.x);
    }
    const rawAngle = angle;
    angle = canonicalLineAngle(angle);
    let normalizedOffset = Number.isFinite(l.offset) ? l.offset : 0;
    // canonicalLineAngle may reverse the direction vector by 180 degrees.
    // Reverse the signed normal offset at the same time to preserve the line.
    if (Math.cos(rawAngle - angle) < 0) normalizedOffset = -normalizedOffset;
    const p2 = (l.p2 && Number.isFinite(l.p2.x) && Number.isFinite(l.p2.y))
      ? l.p2
      : { x: l.p1.x + Math.cos(angle) * Math.max(span, 1000), y: l.p1.y + Math.sin(angle) * Math.max(span, 1000) };
    const len = dist(l.p1, p2);
    if (!Number.isFinite(len) || len < 0.5) continue;

    const signedOffset = lineSignedNormalOffset({ p1: l.p1, offset: normalizedOffset }, angle);
    const isDup = result.some(ex =>
      lineAngleDiff(ex.angle, angle) <= angleTolerance &&
      Math.abs(lineSignedNormalOffset(ex, angle) - signedOffset) <= positionTolerance
    );

    if (!isDup) {
      result.push({
        p1: { x: l.p1.x, y: l.p1.y },
        p2: { x: p2.x, y: p2.y },
        angle: angle,
        offset: normalizedOffset,
        importance: l.importance || 0,
        support: l.support || 0,
        source: l.source || "geometry"
      });
    }
  }
  return result;
}

function buildCollisionSafeLines(lines, features, mergeDist, referenceBounds) {
  const result = filterUniqueLines(lines, mergeDist, referenceBounds);
  const supportPoints = [];

  if (features) {
    for (const a of (features.anchors || [])) {
      if (a && Number.isFinite(a.x) && Number.isFinite(a.y)) supportPoints.push(a);
    }
    for (const p of (features.points || [])) {
      if (p && Number.isFinite(p.x) && Number.isFinite(p.y)) supportPoints.push(p);
    }
    for (const h of (features.handles || [])) {
      if (h && h.handle && Number.isFinite(h.handle.x) && Number.isFinite(h.handle.y)) supportPoints.push(h.handle);
    }
  }

  // A line passing through several real anchors is usually a useful construction
  // alignment. Do not delete it as a collision: reward its geometric support.
  for (const line of result) {
    const nx = -Math.sin(line.angle);
    const ny = Math.cos(line.angle);
    const offset = lineSignedNormalOffset(line, line.angle);
    let support = 0;
    for (const p of supportPoints) {
      const d = Math.abs(p.x * nx + p.y * ny - offset);
      if (d <= Math.max(1.5, positionlessTolerance(mergeDist) * 0.18)) support++;
    }
    line.support = Math.max(line.support || 0, support);
    line._rank = (line.importance || 0) + Math.min(24, line.support * 2.5);
  }

  result.sort((a, b) => b._rank - a._rank);
  for (const line of result) delete line._rank;
  return result;
}

function positionlessTolerance(value) {
  return Math.max(0.5, Number(value) || 1);
}

function detectDominantDirectionPrecise(segments, fallbackAngle) {
  if (!segments || !segments.length) return Number.isFinite(fallbackAngle) ? canonicalLineAngle(fallbackAngle) : 0;
  const bins = 180;
  const weights = new Array(bins).fill(0);
  const angles = [];

  for (const s of segments) {
    if (!s || !s.p1 || !s.p2) continue;
    const len = dist(s.p1, s.p2);
    if (len < 0.5) continue;
    const angle = canonicalLineAngle(Math.atan2(s.p2.y - s.p1.y, s.p2.x - s.p1.x));
    const idx = Math.round(angle / Math.PI * bins) % bins;
    weights[idx] += len;
    angles.push({ angle, weight: len });
  }

  if (!angles.length) return Number.isFinite(fallbackAngle) ? canonicalLineAngle(fallbackAngle) : 0;
  let best = 0;
  for (let i = 1; i < bins; i++) if (weights[i] > weights[best]) best = i;
  const peakAngle = best / bins * Math.PI;
  let sumX = 0, sumY = 0;
  for (const item of angles) {
    if (lineAngleDiff(item.angle, peakAngle) > 4.0 * DEG) continue;
    sumX += Math.cos(item.angle * 2) * item.weight;
    sumY += Math.sin(item.angle * 2) * item.weight;
  }
  if (Math.hypot(sumX, sumY) < EPS) return peakAngle;
  return canonicalLineAngle(0.5 * Math.atan2(sumY, sumX));
}

function cubicExtremaParametersAccurate(b) {
  return cubicExtremaParameters(b);
}

function cubicInflectionParametersAccurate(b) {
  return cubicInflectionParameters(b);
}

function getExactCurveBounds(polyCurve) {
  if (!polyCurve || !polyCurve.curveCount) return null;
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  function include(p) {
    if (!p || !Number.isFinite(p.x) || !Number.isFinite(p.y)) return;
    minX = Math.min(minX, p.x);
    minY = Math.min(minY, p.y);
    maxX = Math.max(maxX, p.x);
    maxY = Math.max(maxY, p.y);
  }
  for (let c = 0; c < polyCurve.curveCount; c++) {
    const curve = polyCurve.at(c);
    for (const b of collectBeziers(curve)) {
      include(b.start);
      include(b.end);
      for (const t of cubicExtremaParametersAccurate(b)) include(cubicPoint(b, t));
    }
  }
  if (!Number.isFinite(minX) || !Number.isFinite(minY) || !Number.isFinite(maxX) || !Number.isFinite(maxY)) return null;
  return {
    x: minX, y: minY,
    width: Math.max(0.001, maxX - minX),
    height: Math.max(0.001, maxY - minY)
  };
}

function addAlignmentLineCandidates(points, origin, angle, tolerance, output, baseImportance, source) {
  if (!points || points.length < 2) return;
  const nx = -Math.sin(angle), ny = Math.cos(angle);
  const ux = Math.cos(angle), uy = Math.sin(angle);
  const records = [], seenCoordinates = new Set();
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const p of points) {
    if (!p || !Number.isFinite(p.x) || !Number.isFinite(p.y)) continue;
    const key = Math.round(p.x * 2) + "," + Math.round(p.y * 2);
    if (seenCoordinates.has(key)) continue;
    seenCoordinates.add(key);
    minX = Math.min(minX,p.x); minY = Math.min(minY,p.y);
    maxX = Math.max(maxX,p.x); maxY = Math.max(maxY,p.y);
    records.push({value:(p.x-origin.x)*nx+(p.y-origin.y)*ny,along:(p.x-origin.x)*ux+(p.y-origin.y)*uy,x:p.x,y:p.y,importance:p.importance||p.priority||0});
  }
  if(records.length<2)return;
  records.sort((x,y)=>x.value-y.value);
  const diagonal=Math.max(1,Math.hypot(maxX-minX,maxY-minY));
  const minAlongSpan=Math.max(tolerance*2.5,diagonal*0.025);
  const clusters=[];
  for(const record of records){
    const current=clusters[clusters.length-1];
    if(!current||Math.abs(record.value-current.mean)>tolerance){
      clusters.push({sum:record.value,count:1,mean:record.value,maxImportance:record.importance,records:[record]});
    }else{
      current.sum+=record.value;current.count++;current.mean=current.sum/current.count;
      current.maxImportance=Math.max(current.maxImportance,record.importance);current.records.push(record);
    }
  }
  const rankedClusters=[];
  for(const cluster of clusters){
    if(cluster.records.length<2)continue;
    let minAlong=Infinity,maxAlong=-Infinity;
    for(const record of cluster.records){minAlong=Math.min(minAlong,record.along);maxAlong=Math.max(maxAlong,record.along);}
    if(maxAlong-minAlong<minAlongSpan)continue;
    const support=cluster.records.length;
    rankedClusters.push({cluster,support,score:baseImportance+Math.min(18,cluster.maxImportance*0.12)+Math.min(14,support*1.4)});
  }
  rankedClusters.sort((x,y)=>y.score-x.score);
  for(const entry of rankedClusters.slice(0,10)){
    const cluster=entry.cluster;
    output.push({p1:{x:origin.x+nx*cluster.mean,y:origin.y+ny*cluster.mean},angle,importance:entry.score,support:entry.support,source:source||"alignment"});
  }
}
function addCurveExtremumTangents(polyCurve, output) {
  if (!polyCurve || !polyCurve.curveCount) return;
  for (let c = 0; c < polyCurve.curveCount; c++) {
    const curve = polyCurve.at(c);
    for (const b of collectBeziers(curve)) {
      const params = cubicExtremaParametersAccurate(b);
      for (const t of params) {
        const mt = 1 - t;
        const dx = 3 * mt * mt * (b.c1.x - b.start.x) +
          6 * mt * t * (b.c2.x - b.c1.x) +
          3 * t * t * (b.end.x - b.c2.x);
        const dy = 3 * mt * mt * (b.c1.y - b.start.y) +
          6 * mt * t * (b.c2.y - b.c1.y) +
          3 * t * t * (b.end.y - b.c2.y);
        const magnitude = Math.hypot(dx, dy);
        if (magnitude < EPS) continue;
        output.push({
          p1: cubicPoint(b, t),
          angle: Math.atan2(dy, dx),
          importance: 82,
          support: 1,
          source: "curve-extremum"
        });
      }
    }
  }
}

function addBezierTangentCandidates(polyCurve, handles, output, includeRawCurves) {
  for (const h of (handles || [])) {
    if (!h || !h.anchor || !h.handle) continue;
    const dx = h.handle.x - h.anchor.x;
    const dy = h.handle.y - h.anchor.y;
    if (Math.hypot(dx, dy) < 0.5) continue;
    output.push({
      p1: { x: h.anchor.x, y: h.anchor.y },
      angle: Math.atan2(dy, dx),
      importance: 54,
      support: 1,
      source: "bezier-handle"
    });
  }

  if (!includeRawCurves || !polyCurve || !polyCurve.curveCount) return;
  for (let c = 0; c < polyCurve.curveCount; c++) {
    const curve = polyCurve.at(c);
    for (const b of collectBeziers(curve)) {
      const vectors = [
        { p: b.start, dx: b.c1.x - b.start.x, dy: b.c1.y - b.start.y },
        { p: b.end, dx: b.end.x - b.c2.x, dy: b.end.y - b.c2.y }
      ];
      for (const v of vectors) {
        if (Math.hypot(v.dx, v.dy) < 1e-9) continue;
        output.push({ p1: v.p, angle: Math.atan2(v.dy, v.dx), importance: 58, support: 1, source: "bezier-tangent" });
      }
      for (const t of cubicInflectionParametersAccurate(b)) {
        const mt = 1 - t;
        const dx = 3 * mt * mt * (b.c1.x - b.start.x) + 6 * mt * t * (b.c2.x - b.c1.x) + 3 * t * t * (b.end.x - b.c2.x);
        const dy = 3 * mt * mt * (b.c1.y - b.start.y) + 6 * mt * t * (b.c2.y - b.c1.y) + 3 * t * t * (b.end.y - b.c2.y);
        if (Math.hypot(dx, dy) < 0.5) continue;
        output.push({ p1: cubicPoint(b, t), angle: Math.atan2(dy, dx), importance: 42, support: 1, source: "bezier-inflection" });
      }
    }
  }
}

function addBoundingBoxGuides(bounds, output, includeDiagonals) {
  if (!bounds) return;
  const x1 = bounds.x, x2 = bounds.x + bounds.width;
  const y1 = bounds.y, y2 = bounds.y + bounds.height;
  const cx = (x1 + x2) / 2, cy = (y1 + y2) / 2;

  // Frame edges are clipped to the real logo bounds at output time.
  output.push({ p1: { x: cx, y: y1 }, angle: 0, importance: 98, source: "bounding-box-edge" });
  output.push({ p1: { x: cx, y: y2 }, angle: 0, importance: 98, source: "bounding-box-edge" });
  output.push({ p1: { x: x1, y: cy }, angle: Math.PI / 2, importance: 98, source: "bounding-box-edge" });
  output.push({ p1: { x: x2, y: cy }, angle: Math.PI / 2, importance: 98, source: "bounding-box-edge" });

  // Centre axes follow the selected reach boundary (logo margin or spread).
  output.push({ p1: { x: cx, y: cy }, angle: 0, importance: 91, source: "centerline" });
  output.push({ p1: { x: cx, y: cy }, angle: Math.PI / 2, importance: 91, source: "centerline" });

  const ratio = Math.abs(bounds.width - bounds.height) / Math.max(bounds.width, bounds.height, 1);
  if (includeDiagonals && ratio <= 0.12) {
    output.push({ p1: { x: cx, y: cy }, angle: Math.atan2(bounds.height, bounds.width), importance: 52, source: "bounding-box-diagonal" });
    output.push({ p1: { x: cx, y: cy }, angle: -Math.atan2(bounds.height, bounds.width), importance: 52, source: "bounding-box-diagonal" });
  }
}

// Seleção visual dos handles: conserva as coordenadas Bézier reais, reduz
// marcadores quando existe espaço e omite os que inevitavelmente colidiriam.
// Isto afeta apenas a apresentação, nunca a geometria da curva original.
function buildCollisionSafeHandles(handles, anchors, baseHandleSize, allowScaling) {
  if (!handles || handles.length === 0) return [];

  const baseRadius = Math.max(0.5, baseHandleSize / 2);
  const minRadius = Math.max(0.8, Math.min(1.15, baseRadius * 0.25));
  const clearanceGap = 0.75;

  const candidates = handles.map((h, index) => {
    let nearestHandle = Infinity;
    for (const other of handles) {
      if (other === h) continue;
      const d = dist(h.handle, other.handle);
      if (d > EPS) nearestHandle = Math.min(nearestHandle, d);
      else nearestHandle = 0;
    }

    // O limite da âncora é aproximado pelo raio circunscrito do quadrado.
    // Assim o círculo do handle não invade a área do nó.
    let anchorRoom = Infinity;
    for (const a of anchors || []) {
      const half = Math.max(0, a.halfSize || 0);
      const anchorExtent = Math.SQRT2 * half;
      anchorRoom = Math.min(
        anchorRoom,
        dist(h.handle, a) - anchorExtent - clearanceGap
      );
    }

    let radius = baseRadius;
    if (allowScaling) {
      radius = Math.min(
        baseRadius,
        Number.isFinite(nearestHandle) ? nearestHandle * 0.38 : baseRadius,
        Number.isFinite(anchorRoom) ? anchorRoom * 0.88 : baseRadius
      );
    }

    return Object.assign({}, h, {
      dotRadius: radius,
      _originalIndex: index,
      _anchorRoom: anchorRoom,
      _priority: (h.priority || h.importance || 0) + (h.baseLength || 0) * 0.001
    });
  });

  // Preserva primeiro os handles mais importantes; em conflitos, o de menor
  // prioridade é omitido em vez de empilhar círculos e hastes no mesmo local.
  candidates.sort((a, b) => b._priority - a._priority);
  const accepted = [];

  for (const h of candidates) {
    if (!Number.isFinite(h.dotRadius) || h.dotRadius <= 0) continue;
    if (allowScaling && h.dotRadius < minRadius) continue;

    // Se o tamanho fixo não couber junto a um nó, ocultar este handle é mais
    // limpo do que desenhar os dois marcadores sobrepostos.
    if (Number.isFinite(h._anchorRoom) && h._anchorRoom < h.dotRadius) continue;

    let collision = false;
    for (const other of accepted) {
      const required = h.dotRadius + other.dotRadius + clearanceGap;
      if (dist(h.handle, other.handle) < required) {
        collision = true;
        break;
      }
    }
    if (collision) continue;
    accepted.push(h);
  }

  accepted.sort((a, b) => a._originalIndex - b._originalIndex);
  return accepted.map(h => {
    delete h._originalIndex;
    delete h._anchorRoom;
    delete h._priority;
    return h;
  });
}


// -----------------------------------------------------------------------------
// Advanced geometry analysis layer.
// This layer consumes the existing analysis output but never changes the
// original anchor topology, Bézier coordinates, handles or radial-petal data.
// -----------------------------------------------------------------------------
function bezierDerivative(b, t) {
  const mt = 1 - t;
  return {
    x: 3 * mt * mt * (b.c1.x - b.start.x) +
       6 * mt * t * (b.c2.x - b.c1.x) +
       3 * t * t * (b.end.x - b.c2.x),
    y: 3 * mt * mt * (b.c1.y - b.start.y) +
       6 * mt * t * (b.c2.y - b.c1.y) +
       3 * t * t * (b.end.y - b.c2.y)
  };
}

function collectDirectionEvidence(polyCurve, geom) {
  const evidence = [];
  let totalWeight = 0;
  let straightWeight = 0;
  let curveWeight = 0;
  let primitiveId = 0;
  const bounds = geom && geom.bounds ? geom.bounds : { width: 100, height: 100 };
  const diagonal = Math.max(1, Math.hypot(bounds.width, bounds.height));
  const minUsefulLength = Math.max(0.5, diagonal * 0.002);

  // Straight vector edges retain their true length and direction.
  for (const seg of (geom.straightSegments || [])) {
    if (!seg || !seg.p1 || !seg.p2) continue;
    const length = dist(seg.p1, seg.p2);
    if (length < minUsefulLength) continue;
    const angle = canonicalLineAngle(Math.atan2(seg.p2.y - seg.p1.y, seg.p2.x - seg.p1.x));
    const weight = Math.min(length, diagonal * 0.75);
    evidence.push({ angle, weight, source: 'edge', primitive: 'edge-' + primitiveId++ });
    straightWeight += weight;
    totalWeight += weight;
  }

  // Curves contribute sampled tangent directions weighted by local arc length.
  // A curve is sampled at five intervals, not at its anchors alone. This allows
  // curve families to contribute without letting a highly subdivided path
  // overwhelm the evidence from genuine straight structural edges.
  if (polyCurve && polyCurve.curveCount) {
    for (let c = 0; c < polyCurve.curveCount; c++) {
      const curve = polyCurve.at(c);
      const beziers = collectBeziers(curve);
      for (let bIdx = 0; bIdx < beziers.length; bIdx++) {
        const b = beziers[bIdx];
        const primitive = 'curve-' + c + '-' + bIdx;
        const samples = [];
        for (let i = 0; i <= 5; i++) samples.push(cubicPoint(b, i / 5));
        let localCurveWeight = 0;
        for (let i = 0; i < 5; i++) {
          const p1 = samples[i], p2 = samples[i + 1];
          const length = dist(p1, p2);
          if (length < minUsefulLength * 0.35) continue;
          const t = (i + 0.5) / 5;
          const d = bezierDerivative(b, t);
          const magnitude = Math.hypot(d.x, d.y);
          if (magnitude < EPS) continue;
          const angle = canonicalLineAngle(Math.atan2(d.y, d.x));
          const weight = Math.min(length, diagonal * 0.18) * 0.68;
          evidence.push({ angle, weight, source: 'curve', primitive });
          localCurveWeight += weight;
          totalWeight += weight;
        }
        curveWeight += Math.min(localCurveWeight, diagonal * 0.65);
      }
    }
  }

  return { samples: evidence, totalWeight, straightWeight, curveWeight, diagonal };
}

function detectDirectionFamilies(evidence, fallbackAngle) {
  const samples = evidence && evidence.samples ? evidence.samples.filter(s =>
    s && Number.isFinite(s.angle) && Number.isFinite(s.weight) && s.weight > EPS
  ) : [];
  if (!samples.length) {
    return Number.isFinite(fallbackAngle)
      ? [{ angle: canonicalLineAngle(fallbackAngle), weight: 1, share: 1, confidence: 0.25, supportCount: 1, straightSupport: 0, curveSupport: 0 }]
      : [];
  }

  const totalWeight = samples.reduce((sum, s) => sum + s.weight, 0) || 1;
  const binCount = 180;
  const histogram = new Array(binCount).fill(0);
  for (const sample of samples) {
    const index = Math.round(canonicalLineAngle(sample.angle) / Math.PI * binCount) % binCount;
    histogram[index] += sample.weight;
  }

  // Smooth adjacent angular bins to avoid unstable peaks at bin boundaries.
  const kernel = [0.12, 0.38, 1, 0.38, 0.12];
  const smooth = new Array(binCount).fill(0);
  for (let i = 0; i < binCount; i++) {
    for (let k = -2; k <= 2; k++) {
      smooth[i] += histogram[(i + k + binCount) % binCount] * kernel[k + 2];
    }
  }

  const peaks = [];
  for (let i = 0; i < binCount; i++) {
    const prev = smooth[(i - 1 + binCount) % binCount];
    const next = smooth[(i + 1) % binCount];
    if (smooth[i] >= prev && smooth[i] > next && smooth[i] > totalWeight * 0.025) {
      peaks.push({ index: i, score: smooth[i], angle: i / binCount * Math.PI });
    }
  }
  peaks.sort((a, b) => b.score - a.score);

  const families = [];
  const assigned = new Set();
  const clusterRadius = 5.0 * DEG;
  const separation = 11.0 * DEG;

  // At most 16 peak candidates are examined, with one linear pass per peak.
  for (const peak of peaks.slice(0, 16)) {
    if (families.length >= 4) break;
    if (families.some(f => lineAngleDiff(f.angle, peak.angle) < separation)) continue;

    let sumX = 0, sumY = 0, weight = 0;
    const primitives = new Set();
    let straightSupport = 0, curveSupport = 0;
    const memberIndices = [];
    for (let i = 0; i < samples.length; i++) {
      if (assigned.has(i)) continue;
      const sample = samples[i];
      if (lineAngleDiff(sample.angle, peak.angle) > clusterRadius) continue;
      memberIndices.push(i);
      sumX += Math.cos(sample.angle * 2) * sample.weight;
      sumY += Math.sin(sample.angle * 2) * sample.weight;
      weight += sample.weight;
      primitives.add(sample.primitive);
      if (sample.source === 'edge') straightSupport += sample.weight;
      else curveSupport += sample.weight;
    }
    if (!memberIndices.length || weight <= 0) continue;

    const angle = canonicalLineAngle(0.5 * Math.atan2(sumY, sumX));
    if (families.some(f => lineAngleDiff(f.angle, angle) < separation)) continue;
    const share = weight / totalWeight;
    const supportCount = primitives.size;

    // A single long straight edge may define a real direction. A curved
    // primitive, however, must never create a direction family by itself:
    // its sampled tangents describe local curvature, not a global grid axis.
    const edgePrimitives = new Set(), curvePrimitives = new Set();
    for (const index of memberIndices) {
      const sample = samples[index];
      if (sample.source === 'edge') edgePrimitives.add(sample.primitive);
      else curvePrimitives.add(sample.primitive);
    }
    const edgePrimitiveCount = edgePrimitives.size;
    const curvePrimitiveCount = curvePrimitives.size;
    if (edgePrimitiveCount === 0 && curvePrimitiveCount < 2) continue;
    if (share < 0.085 && !(share >= 0.055 && supportCount >= 3)) continue;
    if (edgePrimitiveCount > 0 && supportCount < 2 && share < 0.22) continue;
    if (edgePrimitiveCount === 0 && (curvePrimitiveCount < 2 || share < 0.11)) continue;

    for (const index of memberIndices) assigned.add(index);
    families.push({
      angle,
      weight,
      share,
      confidence: clamp(0.42 + share * 1.55 + Math.min(0.12, supportCount * 0.018), 0, 1),
      supportCount,
      straightSupport,
      curveSupport
    });
  }

  families.sort((a, b) => b.weight - a.weight);
  return families;
}
function mergeProjectedPositions(points, angle, tolerance) {
  const nx = -Math.sin(angle), ny = Math.cos(angle);
  const values = [];
  for (const p of points) {
    if (!p || !Number.isFinite(p.x) || !Number.isFinite(p.y)) continue;
    values.push(p.x * nx + p.y * ny);
  }
  values.sort((a, b) => a - b);
  const merged = [];
  for (const value of values) {
    const last = merged[merged.length - 1];
    if (last && Math.abs(value - last.mean) <= tolerance) {
      last.sum += value;
      last.count++;
      last.mean = last.sum / last.count;    } else {
      merged.push({ mean: value, sum: value, count: 1 });
    }
  }
  return merged;
}

function evaluateProjectedModule(points, bounds, angle, directionWeight) {
  const diagonal = Math.max(1, Math.hypot(bounds.width, bounds.height));
  const tolerance = Math.max(0.65, Math.min(2.2, diagonal * 0.0022));
  const positions = mergeProjectedPositions(points, angle, tolerance);
  if (positions.length < 5) return null;

  const gaps = [];
  for (let i = 1; i < positions.length; i++) {
    const gap = positions[i].mean - positions[i - 1].mean;
    if (gap >= Math.max(2.8, diagonal * 0.008) && gap <= diagonal * 0.55) gaps.push(gap);
  }
  if (gaps.length < 3) return null;

  const minUnit = Math.max(3.2, diagonal * 0.009);
  const maxUnit = diagonal * 0.36;
  const rawCandidates = [];
  for (const gap of gaps) {
    for (let divisor = 1; divisor <= 4; divisor++) {
      const unit = gap / divisor;
      if (unit >= minUnit && unit <= maxUnit) rawCandidates.push(unit);
    }
  }
  if (!rawCandidates.length) return null;

  rawCandidates.sort((a, b) => a - b);
  const clusters = [];
  for (const value of rawCandidates) {
    const last = clusters[clusters.length - 1];
    if (!last || Math.abs(value - last.mean) > Math.max(tolerance * 1.5, value * 0.035)) {
      clusters.push({ sum: value, count: 1, mean: value });
    } else {
      last.sum += value;
      last.count++;
      last.mean = last.sum / last.count;
    }
  }
  clusters.sort((a, b) => b.count - a.count);

  let best = null;
  for (const cluster of clusters.slice(0, 48)) {
    const unit = cluster.mean;
    if (unit < minUnit || unit > maxUnit) continue;
    const gapTolerance = Math.max(tolerance * 2.0, unit * 0.04);
    let matchedGaps = 0;
    let directHits = 0;
    let weightedGapSupport = 0;
    for (const gap of gaps) {
      const multiple = Math.max(1, Math.min(4, Math.round(gap / unit)));
      const error = Math.abs(gap - multiple * unit);
      if (error <= gapTolerance) {
        matchedGaps++;
        weightedGapSupport += 1 / multiple;
        if (multiple === 1) directHits++;
      }
    }
    const gapCoverage = matchedGaps / gaps.length;
    if (gapCoverage < 0.70) continue;

    // Search for the most coherent lattice phase using a bounded circular
    // histogram. This is linear in the number of projected points.
    const binCount = 120;
    const bins = new Array(binCount).fill(0);
    for (const p of positions) {
      const residue = ((p.mean % unit) + unit) % unit;
      const index = Math.min(binCount - 1, Math.floor(residue / unit * binCount));
      bins[index] += p.count;
    }
    const phaseTolerance = Math.max(tolerance * 1.65, unit * 0.04);
    const radiusBins = Math.max(1, Math.ceil(phaseTolerance / unit * binCount));
    let phaseBin = 0, phaseVote = -1;
    for (let i = 0; i < binCount; i++) {
      let vote = 0;
      for (let d = -radiusBins; d <= radiusBins; d++) vote += bins[(i + d + binCount) % binCount];
      if (vote > phaseVote) {
        phaseVote = vote;
        phaseBin = i;
      }
    }

    let phase = ((phaseBin + 0.5) / binCount) * unit;
    let cosSum = 0, sinSum = 0;
    for (const p of positions) {
      const residue = ((p.mean % unit) + unit) % unit;
      const delta = ((residue - phase) % unit + unit) % unit;
      if (Math.min(delta, unit - delta) <= phaseTolerance) {
        const radians = residue / unit * Math.PI * 2;
        cosSum += Math.cos(radians) * p.count;
        sinSum += Math.sin(radians) * p.count;
      }
    }
    if (Math.hypot(cosSum, sinSum) > EPS) {
      phase = ((Math.atan2(sinSum, cosSum) / (Math.PI * 2) * unit) % unit + unit) % unit;
    }

    let phaseHits = 0;
    for (const p of positions) {
      const residue = ((p.mean % unit) + unit) % unit;
      const delta = ((residue - phase) % unit + unit) % unit;
      if (Math.min(delta, unit - delta) <= phaseTolerance) phaseHits += p.count;
    }
    const phaseCoverage = phaseHits / Math.max(1, positions.reduce((sum, p) => sum + p.count, 0));

    // A small divisor can make nearly any interval look modular. Demand at
    // least three direct base intervals before accepting a modular unit.
    if (directHits < 3) continue;
    if (phaseCoverage < 0.78) continue;

    const directConfidence = Math.min(1, directHits / 4);
    const confidence = clamp(phaseCoverage * 0.52 + gapCoverage * 0.32 + directConfidence * 0.16, 0, 1);
    if (confidence < 0.78) continue;

    const ratios = [1, 2, 3, 4].filter(n => gaps.some(g =>
      Math.abs(g - unit * n) <= Math.max(tolerance * 2.0, unit * 0.04)
    ));
    const score = directHits * 4.2 + weightedGapSupport * 1.4 + phaseCoverage * 9 + gapCoverage * 6 + (directionWeight || 0) * 0.0005;
    const result = {
      angle: canonicalLineAngle(angle),
      module: unit,
      phase,
      confidence,
      score,
      support: matchedGaps,
      directHits,
      phaseCoverage,
      gapCoverage,
      tolerance,
      ratios,
      pointCount: positions.length
    };
    if (!best || result.score > best.score) best = result;
  }
  return best;
}

function detectModularSystems(geom, directionFamilies) {
  const bounds = geom.bounds;
  const points = [];
  const seen = [];
  function addPoint(p) {
    if (!p || !Number.isFinite(p.x) || !Number.isFinite(p.y)) return;
    if (seen.some(q => dist(q, p) < 0.45)) return;
    seen.push(p);
    points.push({ x: p.x, y: p.y });
  }
  for (const a of (geom.anchors || [])) addPoint(a);
  for (const l of (geom.landmarks || [])) addPoint(l);
  if (points.length > 180) {
    // Preserve structural points first; avoid unbounded O(n log n) candidate work.
    points.length = 180;
  }
  if (points.length < 4) return { module: 0, phase: 0, angle: 0, ratios: [], confidence: 0, axes: [] };

  const axesToTest = [];
  function addAxis(angle, weight, source) {
    const a = canonicalLineAngle(angle);
    if (axesToTest.some(x => lineAngleDiff(x.angle, a) < 2.0 * DEG)) return;
    axesToTest.push({ angle: a, weight: weight || 0, source: source || 'direction-family' });
  }
  for (const family of (directionFamilies || []).slice(0, 4)) {
    addAxis(family.angle, family.weight, 'family');
    addAxis(family.angle + Math.PI / 2, family.weight * 0.88, 'perpendicular');
  }
  if (!axesToTest.length) {
    const fallback = geom.dominantAngle || 0;
    addAxis(fallback, 0, 'fallback');
    addAxis(fallback + Math.PI / 2, 0, 'fallback-perpendicular');
  }

  const results = [];
  for (const axis of axesToTest.slice(0, 8)) {
    const result = evaluateProjectedModule(points, bounds, axis.angle, axis.weight);
    if (!result) continue;
    result.source = axis.source;
    results.push(result);
  }
  results.sort((a, b) => b.score - a.score);

  const selected = [];
  for (const candidate of results) {
    const duplicate = selected.some(existing =>
      lineAngleDiff(existing.angle, candidate.angle) < 2.0 * DEG &&
      Math.abs(existing.module - candidate.module) <= Math.max(1.2, candidate.module * 0.035)
    );
    if (duplicate) continue;
    selected.push(candidate);
    if (selected.length >= 4) break;
  }
  const primary = selected[0] || null;
  return {
    module: primary ? primary.module : 0,
    phase: primary ? primary.phase : 0,
    angle: primary ? primary.angle : 0,
    ratios: primary ? primary.ratios : [],
    confidence: primary ? primary.confidence : 0,
    axes: selected,
    pointCount: points.length
  };
}

function approximateSmallRatio(value, maxTerm) {
  if (!Number.isFinite(value) || value <= 0) return null;
  let best = null;
  let bestError = Infinity;
  for (let denominator = 1; denominator <= (maxTerm || 6); denominator++) {
    const numerator = Math.max(1, Math.round(value * denominator));
    if (numerator > (maxTerm || 6)) continue;
    const ratio = numerator / denominator;
    const error = Math.abs(value - ratio) / Math.max(value, ratio);
    if (error < bestError) {
      bestError = error;
      best = { numerator, denominator, value: ratio, error };
    }
  }
  return best && best.error <= 0.018 ? best : null;
}

function refineCircleCandidates(rawCircles, bounds) {
  const diagonal = Math.max(1, Math.hypot(bounds.width, bounds.height));
  const minRadius = Math.max(2.5, diagonal * 0.0035);
  const maxRadius = diagonal * 2.25;
  const centreTolerance = Math.max(1.5, diagonal * 0.0045);
  const unique = [];

  for (const input of (rawCircles || [])) {
    if (!input || !Number.isFinite(input.cx) || !Number.isFinite(input.cy) || !Number.isFinite(input.r)) continue;
    if (input.r < minRadius || input.r > maxRadius) continue;
    const confidence = Number.isFinite(input.confidence) ? clamp(input.confidence, 0, 1) : 0.58;
    if (confidence < 0.16) continue;
    const margin = diagonal * 1.25;
    if (input.cx < bounds.x - margin || input.cx > bounds.x + bounds.width + margin ||
        input.cy < bounds.y - margin || input.cy > bounds.y + bounds.height + margin) continue;

    const existing = unique.find(c =>
      Math.hypot(c.cx - input.cx, c.cy - input.cy) <= centreTolerance &&
      Math.abs(c.r - input.r) <= Math.max(1.2, input.r * 0.022)
    );
    if (existing) {
      const total = existing.weight + confidence;
      existing.cx = (existing.cx * existing.weight + input.cx * confidence) / total;
      existing.cy = (existing.cy * existing.weight + input.cy * confidence) / total;
      existing.r = (existing.r * existing.weight + input.r * confidence) / total;
      existing.confidence = Math.max(existing.confidence, confidence);
      existing.weight = total;
      existing.samples++;
    } else {
      unique.push({
        cx: input.cx, cy: input.cy, r: input.r,
        confidence, weight: confidence, samples: 1
      });
    }
  }

  // Cluster by common centre, then retain radius tiers as separate circles.
  const families = [];
  for (const circle of unique) {
    let family = families.find(f => Math.hypot(f.cx - circle.cx, f.cy - circle.cy) <= centreTolerance * 1.8);
    if (!family) {
      family = { cx: circle.cx, cy: circle.cy, circles: [], centres: [], confidence: 0, centreSpread: 0 };
      families.push(family);
    }
    family.centres.push({ x: circle.cx, y: circle.cy });
    family.circles.push(circle);
    const n = family.circles.length;
    family.cx += (circle.cx - family.cx) / n;
    family.cy += (circle.cy - family.cy) / n;
  }

  const displayCircles = [];
  for (const family of families) {
    family.circles.sort((a, b) => a.r - b.r);
    const radiusTiers = [];
    for (const circle of family.circles) {
      const last = radiusTiers[radiusTiers.length - 1];
      if (last && Math.abs(circle.r - last.r) <= Math.max(1.3, circle.r * 0.022)) {
        const n = last.samples + circle.samples;
        last.r = (last.r * last.samples + circle.r * circle.samples) / n;
        last.confidence = Math.max(last.confidence, circle.confidence);
        last.samples = n;
      } else {
        radiusTiers.push({ r: circle.r, confidence: circle.confidence, samples: circle.samples });
      }
    }
    family.circles = radiusTiers;
    const spread = family.circles.length ? family.circles.reduce((sum, c) => sum + c.confidence, 0) / family.circles.length : 0;
    family.confidence = spread;
    family.centreSpread = family.centres.length > 1
      ? Math.max.apply(null, family.centres.map(p => Math.hypot(p.x - family.cx, p.y - family.cy)))
      : 0;
    family.confidence *= clamp(1 - family.centreSpread / Math.max(centreTolerance * 1.8, EPS), 0.55, 1);
    delete family.centres;

    const radii = family.circles.map(c => c.r);
    const gaps = [];
    for (let i = 1; i < radii.length; i++) gaps.push(radii[i] - radii[i - 1]);
    let radiusModule = 0, radiusModuleConfidence = 0;
    if (gaps.length >= 2) {
      const sortedGaps = gaps.slice().sort((a, b) => a - b);
      const median = sortedGaps[Math.floor(sortedGaps.length / 2)];
      const close = gaps.filter(g => Math.abs(g - median) <= Math.max(1.2, median * 0.045));
      if (median >= minRadius && close.length >= 2) {
        radiusModule = close.reduce((sum, g) => sum + g, 0) / close.length;
        radiusModuleConfidence = close.length / gaps.length * family.confidence;
      }
    }
    family.radiusModule = radiusModule;
    family.radiusModuleConfidence = radiusModuleConfidence;
    family.radiusRatios = [];
    if (radii.length >= 2) {
      const base = radii[0];
      for (let i = 1; i < radii.length; i++) {
        const ratio = approximateSmallRatio(radii[i] / base, 6);
        if (ratio) family.radiusRatios.push({ innerRadius: base, outerRadius: radii[i], ratio, confidence: Math.min(family.confidence, 1 - ratio.error * 8) });
      }
    }

    for (const tier of family.circles) {
      displayCircles.push({ cx: family.cx, cy: family.cy, r: tier.r, confidence: tier.confidence, familySize: family.circles.length });
    }
  }

  displayCircles.sort((a, b) => (b.confidence + Math.min(0.2, b.familySize * 0.04)) - (a.confidence + Math.min(0.2, a.familySize * 0.04)));
  const limitedCircles = displayCircles.slice(0, 48);
  const relationCount = families.reduce((sum, f) => sum + f.radiusRatios.length, 0);
  return { circles: limitedCircles, families, relationCount };
}

function enrichGeometryAnalysis(polyCurve, geom) {
  const evidence = collectDirectionEvidence(polyCurve, geom);
  const families = detectDirectionFamilies(evidence, geom.dominantAngle);
  const primaryAngle = families.length ? families[0].angle : geom.dominantAngle;
  const moduleSystems = detectModularSystems(geom, families);
  const circleAnalysis = refineCircleCandidates(geom.circles, geom.bounds);

  // Derived analysis is attached alongside, never written into the anchors,
  // handles, Bézier records, radial petals or original circle candidates.
  geom.directionEvidence = evidence;
  geom.directionFamilies = families;
  geom.modules = moduleSystems;
  geom.circleFamilies = circleAnalysis.families;
  geom.displayCircles = circleAnalysis.circles;
  geom.circleRelationCount = circleAnalysis.relationCount;
  if (lineAngleDiff(primaryAngle, geom.dominantAngle) > 0.75 * DEG) {
    geom.symmetry = detectAxisSymmetry(geom.anchors, primaryAngle);
  }
  geom.proportionRelations = [];
  for (const axis of moduleSystems.axes) {
    for (const ratio of (axis.ratios || [])) {
      if (ratio > 1) geom.proportionRelations.push({ type: 'linear-module', angle: axis.angle, ratio: ratio, confidence: axis.confidence });
    }
  }
  for (const family of circleAnalysis.families) {
    for (const relation of family.radiusRatios) {
      geom.proportionRelations.push({ type: 'circle-radius', centre: { x: family.cx, y: family.cy }, relation, confidence: relation.confidence });
    }
  }
  return geom;
}

function createModuleGridCandidates(axis, bounds, origin, output, mergeTolerance) {
  if (!axis || !Number.isFinite(axis.module) || axis.module <= 0 || axis.confidence < 0.70) return;
  const nx = -Math.sin(axis.angle), ny = Math.cos(axis.angle);
  const corners = [
    { x: bounds.x, y: bounds.y },
    { x: bounds.x + bounds.width, y: bounds.y },
    { x: bounds.x + bounds.width, y: bounds.y + bounds.height },
    { x: bounds.x, y: bounds.y + bounds.height }
  ];
  const projections = corners.map(p => p.x * nx + p.y * ny);
  const minP = Math.min.apply(null, projections);
  const maxP = Math.max.apply(null, projections);
  const originP = origin.x * nx + origin.y * ny;
  const firstK = Math.ceil((minP - axis.phase - mergeTolerance * 0.15) / axis.module);
  const lastK = Math.floor((maxP - axis.phase + mergeTolerance * 0.15) / axis.module);
  if (lastK < firstK) return;
  // A measured module is a reference unit, not permission to cover the whole
  // canvas with a dense lattice. Keep a compact five-line window around centre.
  const centreK = Math.round((originP - axis.phase) / axis.module);
  const selectedK = [centreK,centreK-1,centreK+1,centreK-2,centreK+2]
    .filter((k,index,array)=>k>=firstK&&k<=lastK&&array.indexOf(k)===index);
  let ordinal = 0;
  for (const k of selectedK) {
    const projection = axis.phase + k * axis.module;
    const offset = projection - originP;
    const major = (ordinal % 2 === 0);
    output.push({
      p1: origin,
      angle: axis.angle,
      offset,
      importance: major ? 70 : 57,
      support: axis.support || 0,
      source: 'modular-grid',
      moduleMajor: major,
      moduleIndex: k,
      moduleValue: axis.module
    });
    ordinal++;
  }
}

function addCircleFamilyConstructionCandidates(circleFamilies, output) {
  for (const family of (circleFamilies || []).slice(0, 4)) {
    if (!family || family.circles.length < 2 || family.confidence < 0.42) continue;
    const circles = family.circles.slice().sort((a, b) => a.r - b.r);
    const hasMeasuredRelation = family.radiusRatios.length > 0 || family.radiusModuleConfidence >= 0.60;
    if (!hasMeasuredRelation) continue;
    // The centre axes and outer ring tangencies express the measured diameters.
    output.push({ p1: { x: family.cx, y: family.cy }, angle: 0, importance: 64, source: 'circle-centre-axis' });
    output.push({ p1: { x: family.cx, y: family.cy }, angle: Math.PI / 2, importance: 64, source: 'circle-centre-axis' });
    for (const circle of circles.slice(0, 3)) {
      const r = circle.r;
      const importance = 48 + circle.confidence * 8;
      output.push({ p1: { x: family.cx + r, y: family.cy }, angle: Math.PI / 2, importance, source: 'circle-ratio-boundary' });
      output.push({ p1: { x: family.cx - r, y: family.cy }, angle: Math.PI / 2, importance, source: 'circle-ratio-boundary' });
      output.push({ p1: { x: family.cx, y: family.cy + r }, angle: 0, importance, source: 'circle-ratio-boundary' });
      output.push({ p1: { x: family.cx, y: family.cy - r }, angle: 0, importance, source: 'circle-ratio-boundary' });
    }
  }
}


function readPickerRGBA(picker, fallback) {
  try {
    const value = picker && picker.value ? picker.value : null;
    const rgba = value && value.rgba8 ? value.rgba8 : value;
    if (rgba && Number.isFinite(rgba.r) && Number.isFinite(rgba.g) && Number.isFinite(rgba.b)) {
      return {
        r: rgba.r,
        g: rgba.g,
        b: rgba.b,
        alpha: Number.isFinite(rgba.alpha) ? rgba.alpha : 255
      };
    }
  } catch (e) {}
  return fallback || { r: 50, g: 60, b: 240, alpha: 160 };
}

function createGridStrokeStyles(picker, baseWidth) {
  const base = readPickerRGBA(picker, { r: 50, g: 60, b: 240, alpha: 160 });
  function makeStyle(alphaScale, widthScale) {
    let fill = FillDescriptor.createNone();
    try {
      fill = FillDescriptor.createSolid(makeColorRGBA(base.r, base.g, base.b, base.alpha * alphaScale));
    } catch (e) {}
    return {
      fill,
      lineStyle: LineStyleDescriptor.createDefault(Math.max(0.1, baseWidth * widthScale))
    };
  }
  return {
    primary: makeStyle(1.0, 1.22),
    secondary: makeStyle(0.78, 0.96),
    auxiliary: makeStyle(0.56, 0.76),
    fadeNear: makeStyle(0.20, 0.58),
    fadeMid: makeStyle(0.38, 0.66),
    fadeFar: makeStyle(0.64, 0.78),
    dimension: makeStyle(0.92, 0.92)
  };
}

function appendStyledGridLine(defs, line, ext, styles, noFill) {
  if (!ext || dist(ext.p1, ext.p2) < 0.75) return;
  function add(a, b, style) {
    if (dist(a, b) < 0.5) return;
    defs.push(PolyCurveNodeDefinition.create(
      makeLinePoly(a.x, a.y, b.x, b.y), noFill, style.fill, style.lineStyle, noFill
    ));
  }

  const isPrimary = line.source === 'structural-edge' ||
    line.source === 'bounding-box-edge' || line.source === 'bounding-box-diagonal' ||
    line.source === 'symmetry-axis' || line.source === 'centerline' ||
    (line.importance || 0) >= 88;
  const isSecondary = line.source === 'modular-grid' ||
    line.source === 'circle-centre-axis' || line.source === 'circle-ratio-boundary' ||
    (line.importance || 0) >= 60;

  if (isPrimary) {
    add(ext.p1, ext.p2, styles.primary);
    return;
  }
  if (isSecondary) {
    add(ext.p1, ext.p2, styles.secondary);
    return;
  }

  // A lightweight five-part taper approximates line fade at both frame edges.
  // The central section remains visible; the real geometry and endpoints do not move.
  const dx = ext.p2.x - ext.p1.x;
  const dy = ext.p2.y - ext.p1.y;
  const tValues = [0, 0.12, 0.28, 0.72, 0.88, 1];
  const segmentStyles = [styles.fadeNear, styles.fadeMid, styles.fadeFar, styles.fadeMid, styles.fadeNear];
  for (let i = 0; i < segmentStyles.length; i++) {
    const a = { x: ext.p1.x + dx * tValues[i], y: ext.p1.y + dy * tValues[i] };
    const b = { x: ext.p1.x + dx * tValues[i + 1], y: ext.p1.y + dy * tValues[i + 1] };
    add(a, b, segmentStyles[i]);
  }
}

function main() {
  if (!doc || !doc.selection || doc.selection.length === 0) {
    alert("Selecione o seu logo (forma, curva ou grupo) para construir as guias geométricas.");
    return;
  }

  const rawSel = toArray(doc.selection.nodes).filter(Boolean);
  if (rawSel.some(isEmbeddedDocumentNode)) {
    alert("O objeto selecionado contém um Documento Embebido (.afdesign, .svg, .pdf).\nConverta em curvas nativas ou edite o documento antes de prosseguir.");
    return;
  }

  const primaryNode = rawSel[0];
  const polyCurve = extractCompositePolyCurve(rawSel);
  if (!polyCurve || polyCurve.curveCount === 0) {
    alert("Não foi possível extrair vetores válidos do objeto ou grupo selecionado.");
    return;
  }

  let spreadExtents = { x: 0, y: 0, width: 2000, height: 2000 };
  try {
    const spread = doc.currentSpread;
    const ext = spread.getSpreadExtents ? spread.getSpreadExtents() : null;
    if (ext && ext.width > 0) spreadExtents = ext;
  } catch (e) {}

  const initialGeom = enrichGeometryAnalysis(polyCurve, analyzeSmartGeometry(polyCurve, 9, 9));
  const initialExactBounds = getExactCurveBounds(polyCurve) || initialGeom.bounds;
  const initialPreciseAngle = initialGeom.directionFamilies && initialGeom.directionFamilies.length
    ? initialGeom.directionFamilies[0].angle
    : detectDominantDirectionPrecise(initialGeom.straightSegments, initialGeom.dominantAngle);
  const initialGridSymmetry = {
    score: initialGeom.symmetry.score,
    axis: initialGeom.symmetry.longitudinal >= initialGeom.symmetry.transverse
      ? initialPreciseAngle
      : initialPreciseAngle + Math.PI / 2
  };
  const isRadial = initialGeom.isRadialArray;
  const isOrthogonalDominant = Math.abs(Math.sin(2 * initialGeom.dominantAngle)) < 0.28;

  // Se for arranjo radial real, ativa modo 1; se for qualquer outro logo (incluindo cruzes e monogramas), ativa modo 0 (Smart Adaptive)
  const initialGridMode = isRadial ? 1 : 0;
  const initialHasCircles = (initialGeom.displayCircles || initialGeom.circles).length > 0;
  const initialHasHandles = initialGeom.hasRealCurves && initialGeom.handles.length > 0;
  const initialHasSymmetry = initialGeom.symmetry.score >= 0.70;
  const initialHasModules = initialGeom.modules.confidence >= 0.70 && initialGeom.modules.axes.length > 0;
  const initialHasInflections = initialGeom.landmarks.some(l => l.type === "inflection");

  const dlg = Dialog.create("Logo Construction & Gridlines");
  dlg.initialWidth = 580;
  dlg.isResizable = true;

  const colLeft = dlg.addColumn();
  const colRight = dlg.addColumn();

  // --- COLUNA 1: Camadas Visuais & Grelha Inteligente (100% Restaurada) ---
  const layerGrp = colLeft.addGroup("1. Visual Layers & Auto-Setup");
  const showOverlaySwitch = layerGrp.addSwitch("Silhouette Overlay (White)", true);
  const overlayOpacityCtrl = layerGrp.addUnitValueEditor("Overlay Opacity (%)", UnitType.Percentage, UnitType.Percentage, 18, 0, 100);
  overlayOpacityCtrl.showPopupSlider = true;
  const showOutlineSwitch = layerGrp.addSwitch("Shape Outline", true);
  const showCirclesSwitch = layerGrp.addSwitch("Curvature Arcs & Rings", initialHasCircles);
  const showGridSwitch = layerGrp.addSwitch("Construction Gridlines", true);
  const showHandlesSwitch = layerGrp.addSwitch("Bezier Handles", initialHasHandles);
  const showAnchorsSwitch = layerGrp.addSwitch("Anchor Nodes", true);

  attachTip(showOverlaySwitch, "Exibe silhueta semitransparente branca de contraste para evidenciar o traçado geométrico.");
  attachTip(overlayOpacityCtrl, "Opacidade percentual da silhueta branca de fundo.");
  attachTip(showOutlineSwitch, "Desenha o contorno vetorial calibrado e nítido das formas do logo.");
  attachTip(showCirclesSwitch, "Exibe círculos concêntricos e arcos circulares de curvatura identificados.");
  attachTip(showGridSwitch, "Gera as linhas estruturais de projeção geométrica e tangentes.");
  attachTip(showHandlesSwitch, "Exibe as hastes e pontos de controlo Bézier em curvas orgânicas.");
  attachTip(showAnchorsSwitch, "Exibe os vértices e nós vetoriais reais da geometria.");

  const gridGrp = colLeft.addGroup("2. Smart Geometry & Grid");
  const gridModeCombo = gridGrp.addComboBox("Grid Alignment", [
    "Smart Adaptive (Dominant Angle)",
    "Radial Outward Projections (Brand Guidelines)",
    "Orthogonal Grid (H/V Lines & Centerlines)",
    "Structural Edges (Edge Extensions)"
  ], initialGridMode);

  const nodeDisplayCombo = gridGrp.addComboBox("Node Display", ["Auto / Smart", "All Anchors", "Structural Landmarks"], 0);
  const adaptiveScaleSwitch = gridGrp.addSwitch("Automatic Collision Control", true);
  const minNodeGapCtrl = gridGrp.addUnitValueEditor("Minimum Visual Gap (px)", UnitType.Pixel, doc.units, 6, 1, 40);
  minNodeGapCtrl.showPopupSlider = true;
  const reachModeCombo = gridGrp.addComboBox("Reach Boundary", ["Logo Bounds + Margin", "Canvas / Spread Bounds"], 0);
  const gridReachCtrl = gridGrp.addUnitValueEditor("Frame Margin (px)", UnitType.Pixel, doc.units, 100, 0, 2000);
  gridReachCtrl.showPopupSlider = true;
  const mergeDistCtrl = gridGrp.addUnitValueEditor("Merge Parallel Lines (px)", UnitType.Pixel, doc.units, 10, 1, 100);
  mergeDistCtrl.showPopupSlider = true;
  const tangentSourceCombo = gridGrp.addComboBox("Vector Source", ["Structural Edges (Clean)", "Structural + Handles", "All Vectors (Raw)"], 0);

  const showSymmetrySwitch = gridGrp.addSwitch("Detected Symmetry", initialHasSymmetry);
  const showModulesSwitch = gridGrp.addSwitch("Proportions / Modules", initialHasModules);
  const showLandmarksSwitch = gridGrp.addSwitch("Geometric Landmarks", false);
  const showInflectionSwitch = gridGrp.addSwitch("Inflection Points", initialHasInflections);

  attachTip(gridModeCombo, "Smart Adaptive combina famílias de direcções suportadas por arestas e tangentes Bézier. Evita impor uma única orientação a logótipos com várias estruturas.");
  attachTip(nodeDisplayCombo, "Controla quais nós são destacados. A análise conserva nós distintos mesmo em curvas muito fechadas; Auto reduz apenas marcadores de baixa prioridade quando há pouco espaço.");
  attachTip(adaptiveScaleSwitch, "Reduz automaticamente marcadores e suprime linhas em áreas densas para evitar poluição visual.");
  attachTip(minNodeGapCtrl, "Distância mínima de segurança entre nós vizinhos para prevenir sobreposições.");
  attachTip(reachModeCombo, "Determina até onde as linhas de projeção se estendem.");
  attachTip(gridReachCtrl, "Distância adicional além do limite do logo para o prolongamento das linhas guia.");
  attachTip(mergeDistCtrl, "Define a tolerância para agrupar linhas paralelas quase coincidentes. Valores maiores reduzem detalhes próximos e tornam a grelha menos densa.");
  attachTip(tangentSourceCombo, "Define a origem das linhas de projeção técnica.");
  attachTip(showSymmetrySwitch, "Traça o eixo mestre de simetria do logo.");
  attachTip(showModulesSwitch, "Detecta módulos lineares repetidos e relações entre raios circulares. Só apresenta sistemas com confiança geométrica suficiente.");
  attachTip(showLandmarksSwitch, "Destaca extremos analíticos, cúspides e pontos estacionários de Bézier que não coincidem com âncoras nativas.");
  attachTip(showInflectionSwitch, "Destaca pontos de inflexão de curvas S.");

  // --- COLUNA 2: Marcadores, Traços & Cores (100% Restaurada) ---
  const dimGrp = colRight.addGroup("3. Marker Dimensions & Style");
  const anchorSizeCtrl = dimGrp.addUnitValueEditor("Anchor Base Size", UnitType.Pixel, doc.units, 9, 2, 40);
  const handleSizeCtrl = dimGrp.addUnitValueEditor("Handle Dot Size", UnitType.Pixel, doc.units, 9, 1, 30);
  const landmarkSizeCtrl = dimGrp.addUnitValueEditor("Landmark Size", UnitType.Pixel, doc.units, 5, 2, 30);

  // Por defeito, usa dimensionamento automático para evitar aglomeração de pontos.
  const handleScalingCombo = dimGrp.addComboBox("Handle Scaling", ["Automatic (Smart Damping)", "Fixed (Strict Dot Size)"], 0);
  const stemScaleCombo = dimGrp.addComboBox("Handle Stem Projection", ["1.0x (Exact Tangent)", "1.5x (Extended)", "2.0x (Bold Projection)", "3.0x (Technical Guide)"], 0);

  const markerStyleOptions = ["Fill + Stroke", "Fill Only", "Stroke Only"];
  const anchorStyleCombo = dimGrp.addComboBox("Anchor Style", markerStyleOptions, 0);
  const handleStyleCombo = dimGrp.addComboBox("Handle Style", markerStyleOptions, 0);
  const landmarkStyleCombo = dimGrp.addComboBox("Landmark Style", markerStyleOptions, 2);

  attachTip(anchorSizeCtrl, "Largura dos nós quadrados das âncoras em pixels.");
  attachTip(handleSizeCtrl, "Diâmetro dos pontos circulares nas extremidades dos handles de Bézier.");
  attachTip(landmarkSizeCtrl, "Diâmetro dos marcadores de ápices e marcos geométricos.");
  attachTip(handleScalingCombo, "'Automatic' reduz pontos em zonas densas e oculta os que colidiriam; 'Fixed' mantém o diâmetro, com filtragem dos conflitos inevitáveis.");
  attachTip(stemScaleCombo, "Mantém o ponto na posição Bézier real; os valores acima de 1x prolongam apenas a haste, para além do ponto.");
  attachTip(anchorStyleCombo, "Estilo de renderização dos nós das âncoras.");
  attachTip(handleStyleCombo, "Estilo de renderização dos círculos dos handles.");
  attachTip(landmarkStyleCombo, "Estilo de renderização dos marcos geométricos.");

  const widthGrp = colRight.addGroup("4. Stroke Widths (pt)");
  const outlineWidthCtrl = widthGrp.addUnitValueEditor("Outline & Arcs Width", UnitType.Point, doc.units, 2.8, 0.1, 10);
  const gridWidthCtrl = widthGrp.addUnitValueEditor("Grid & Guides Width", UnitType.Point, doc.units, 1.0, 0.1, 10);
  const nodeStrokeWidthCtrl = widthGrp.addUnitValueEditor("Nodes & Handles Width", UnitType.Point, doc.units, 1.4, 0.1, 10);

  attachTip(outlineWidthCtrl, "Espessura do contorno principal e dos arcos em pontos.");
  attachTip(gridWidthCtrl, "Espessura das linhas da grelha de construção e eixos estruturais.");
  attachTip(nodeStrokeWidthCtrl, "Espessura da borda dos nós, círculos de handles e hastes de direção.");

  const colorGrp = colRight.addGroup("5. Color Palette");
  const outlineColorPicker = colorGrp.addColourPicker("Outline & Arcs Color", makeColorRGBA(25, 130, 240, 230));
  const gridColorPicker = colorGrp.addColourPicker("Grid & Axis Color", makeColorRGBA(50, 60, 240, 160));
  const stemColorPicker = colorGrp.addColourPicker("Handle Stems Color", makeColorRGBA(245, 150, 20, 230));
  const handleDotFillPicker = colorGrp.addColourPicker("Handle Dots Fill", makeColorRGBA(255, 255, 255, 255));
  const anchorFillPicker = colorGrp.addColourPicker("Anchor Fill Color", makeColorRGBA(25, 25, 30, 255));
  const landmarkFillPicker = colorGrp.addColourPicker("Landmark Fill Color", makeColorRGBA(255, 255, 255, 255));
  const nodeBorderPicker = colorGrp.addColourPicker("Node & Dot Border Color", makeColorRGBA(245, 40, 200, 255));
  const landmarkBorderPicker = colorGrp.addColourPicker("Landmark Border Color", makeColorRGBA(245, 40, 200, 255));

  attachTip(outlineColorPicker, "Cor do contorno vetorial da forma e dos arcos de curvatura.");
  attachTip(gridColorPicker, "Cor das linhas de construção e eixos estruturais.");
  attachTip(stemColorPicker, "Cor das hastes que conectam os nós aos pontos de controle (handles).");
  attachTip(handleDotFillPicker, "Cor de preenchimento dos círculos nos pontos de controle de Bézier.");
  attachTip(anchorFillPicker, "Cor de preenchimento dos quadrados dos nós vetoriais.");
  attachTip(landmarkFillPicker, "Cor de preenchimento dos marcadores de ápices e extremos.");
  attachTip(nodeBorderPicker, "Cor da borda dos nós âncora e pontos de controle.");
  attachTip(landmarkBorderPicker, "Cor da borda dos marcadores de marcos geométricos.");

  const geometryCache = {};
  function getCachedGeometry(anchorSize, handleSize) {
    const key = String(anchorSize) + "|" + String(handleSize);
    if (!geometryCache[key]) {
      const baseGeometry = analyzeSmartGeometry(polyCurve, anchorSize, handleSize);
      geometryCache[key] = enrichGeometryAnalysis(polyCurve, baseGeometry);
    }
    return geometryCache[key];
  }

  function getDisplayAnchors(geom, mode, gap) {
    const source = geom.anchors.slice().sort((a, b) => b.priority - a.priority);
    // O modo "All Anchors" continua a mostrar todos os nós sem filtragem visual.
    if (mode === 1) return source;

    const result = [];
    const threshold = mode === 2 ? Math.max(4, gap * 1.35) : Math.max(3, gap);
    const cellSize = threshold;
    const buckets = new Map();
    function key(x, y) { return x + "," + y; }
    function addToSpatialIndex(point, index) {
      const gx = Math.floor(point.x / cellSize);
      const gy = Math.floor(point.y / cellSize);
      const k = key(gx, gy);
      if (!buckets.has(k)) buckets.set(k, []);
      buckets.get(k).push(index);
    }
    function hasNearby(point) {
      const gx = Math.floor(point.x / cellSize);
      const gy = Math.floor(point.y / cellSize);
      for (let dx = -1; dx <= 1; dx++) {
        for (let dy = -1; dy <= 1; dy++) {
          const bucket = buckets.get(key(gx + dx, gy + dy));
          if (!bucket) continue;
          for (const index of bucket) {
            if (dist(result[index], point) < threshold) return true;
          }
        }
      }
      return false;
    }

    for (const original of source) {
      const a = Object.assign({}, original);
      const protectedFeature = a.corner || a.cusp || a.endpoint || a.extrema ||
        (a.curvatureImportance || 0) >= 7.5;
      // Distinct nodes on compact curves remain separate in the geometry model.
      // Auto only suppresses low-priority marker drawings when they collide visually.
      if (protectedFeature || !hasNearby(a)) {
        const index = result.length;
        result.push(a);
        addToSpatialIndex(a, index);
      }
    }

    const baseHalf = anchorSizeCtrl.value / 2;
    const nearestDistances = calculateNearestDistances(result, Math.max(1, anchorSizeCtrl.value * 2.4));
    return result.map((a, i) => {
      const nearest = nearestDistances[i];
      const halfSize = nearest < anchorSizeCtrl.value * 2.4
        ? Math.max(1.0, Math.min(baseHalf, nearest * 0.32))
        : baseHalf;
      return Object.assign({}, a, { halfSize: halfSize, clearance: nearest });
    });
  }

  // =========================================================================
  // MOTOR GEOMÉTRICO RESTAURADO COM CORTES TRANSVERSAIS INTEGRADOS NA GRELHA
  // =========================================================================
  function buildGridStructure() {
    const geom = getCachedGeometry(anchorSizeCtrl.value, handleSizeCtrl.value);
    const landmarkCoincidenceTolerance = Math.max(
      1e-5,
      Math.hypot(geom.bounds.width, geom.bounds.height) * 1e-7
    );
    const minGap = minNodeGapCtrl.value;
    const smartCollision = adaptiveScaleSwitch.value;
    const isHandleFixed = handleScalingCombo.selectedIndex === 1;

    let displayAnchors = getDisplayAnchors(geom, nodeDisplayCombo.selectedIndex, minGap);
    let displayHandles = geom.handles;

    const stemMultipliers = [1.0, 1.5, 2.0, 3.0];
    const stemMultiplier = stemMultipliers[stemScaleCombo.selectedIndex] || 1.0;

    if (!smartCollision) {
      const baseHalf = anchorSizeCtrl.value / 2;
      displayAnchors = displayAnchors.map(a => Object.assign({}, a, { halfSize: baseHalf }));
    }

    if (isHandleFixed) {
      const baseDot = handleSizeCtrl.value / 2;
      displayHandles = displayHandles.map(h => Object.assign({}, h, { dotRadius: baseDot }));
    }

    // Os handles usados nas guias geométricas continuam completos. A filtragem
    // seguinte é exclusiva da camada visual de hastes e pontos de controlo.
    const handleObstacles = [];
    if (showAnchorsSwitch.value) {
      for (const a of displayAnchors) handleObstacles.push(a);
    }
    if (showLandmarksSwitch.value) {
      for (const l of geom.landmarks) {
        if (l.type !== "extrema" && l.type !== "cusp" && l.type !== "stationary") continue;
        if (geom.anchors.some(a => dist(a, l) <= landmarkCoincidenceTolerance)) continue;
        handleObstacles.push({ x: l.x, y: l.y, halfSize: Math.max(1.0, landmarkSizeCtrl.value / 2) });
      }
    }
    if (showInflectionSwitch.value) {
      for (const l of geom.landmarks) {
        if (l.type === "inflection") {
          handleObstacles.push({ x: l.x, y: l.y, halfSize: Math.max(1.0, handleSizeCtrl.value * 0.35) });
        }
      }
    }
    const visualHandles = smartCollision
      ? buildCollisionSafeHandles(displayHandles, handleObstacles, handleSizeCtrl.value, !isHandleFixed)
      : displayHandles;

    const exactBounds = initialExactBounds || geom.bounds;
    const exactCenter = {
      x: exactBounds.x + exactBounds.width / 2,
      y: exactBounds.y + exactBounds.height / 2
    };
    const preserveRadialBounds = gridModeCombo.selectedIndex === 1 && geom.isRadialArray;
    const framingBounds = preserveRadialBounds ? geom.bounds : exactBounds;
    const constructionBounds = reachModeCombo.selectedIndex === 0
      ? { x: framingBounds.x - gridReachCtrl.value, y: framingBounds.y - gridReachCtrl.value, width: framingBounds.width + gridReachCtrl.value * 2, height: framingBounds.height + gridReachCtrl.value * 2 }
      : spreadExtents;
    // Radial-array construction keeps its established bounds and centre logic.
    const center = geom.center;

    const noFill = FillDescriptor.createNone();
    const overlayAlpha = Math.round(255 * clamp(overlayOpacityCtrl.value, 0, 100) / 100);
    const overlayFill = resolveFillDescriptor(null, 255, 255, 255, overlayAlpha);

    const outlineStroke = resolveFillDescriptor(outlineColorPicker, 25, 130, 240, 230);
    const gridStroke = resolveFillDescriptor(gridColorPicker, 50, 60, 240, 160);
    const stemStroke = resolveFillDescriptor(stemColorPicker, 245, 150, 20, 230);
    const nodeBorderStroke = resolveFillDescriptor(nodeBorderPicker, 245, 40, 200, 255);
    const landmarkBorderStroke = resolveFillDescriptor(landmarkBorderPicker, 245, 40, 200, 255);

    let dotFillDesc = noFill, dotStrokeDesc = noFill;
    if (handleStyleCombo.selectedIndex === 0) {
      dotFillDesc = resolveFillDescriptor(handleDotFillPicker, 255, 255, 255, 255);
      dotStrokeDesc = nodeBorderStroke;
    } else if (handleStyleCombo.selectedIndex === 1) {
      dotFillDesc = resolveFillDescriptor(handleDotFillPicker, 255, 255, 255, 255);
    } else {
      dotStrokeDesc = nodeBorderStroke;
    }

    let anchorFillDesc = noFill, anchorStrokeDesc = noFill;
    if (anchorStyleCombo.selectedIndex === 0) {
      anchorFillDesc = resolveFillDescriptor(anchorFillPicker, 25, 25, 30, 255);
      anchorStrokeDesc = nodeBorderStroke;
    } else if (anchorStyleCombo.selectedIndex === 1) {
      anchorFillDesc = resolveFillDescriptor(anchorFillPicker, 25, 25, 30, 255);
    } else {
      anchorStrokeDesc = nodeBorderStroke;
    }

    let landmarkFillDesc = noFill, landmarkStrokeDesc = noFill;
    if (landmarkStyleCombo.selectedIndex === 0) {
      landmarkFillDesc = resolveFillDescriptor(landmarkFillPicker, 255, 255, 255, 255);
      landmarkStrokeDesc = landmarkBorderStroke;
    } else if (landmarkStyleCombo.selectedIndex === 1) {
      landmarkFillDesc = resolveFillDescriptor(landmarkFillPicker, 255, 255, 255, 255);
    } else {
      landmarkStrokeDesc = landmarkBorderStroke;
    }

    const lsdNone = LineStyleDescriptor.createDefault(0.1);
    const lsdOutline = LineStyleDescriptor.createDefault(outlineWidthCtrl.value);
    const lsdGrid = LineStyleDescriptor.createDefault(gridWidthCtrl.value);
    const gridStrokeStyles = createGridStrokeStyles(gridColorPicker, gridWidthCtrl.value);    const lsdNode = LineStyleDescriptor.createDefault(nodeStrokeWidthCtrl.value);
    const subContainers = [];

    // 0. Logo Overlay
    if (showOverlaySwitch.value && overlayAlpha > 0) {
      subContainers.push({
        name: "0. Logo Overlay",
        defs: [PolyCurveNodeDefinition.create(polyCurve.clone(), overlayFill, noFill, lsdNone, noFill)]
      });
    }

    // 1. Shape Outline
    if (showOutlineSwitch.value) {
      subContainers.push({
        name: "1. Shape Outline",
        defs: [PolyCurveNodeDefinition.create(polyCurve.clone(), noFill, outlineStroke, lsdOutline, noFill)]
      });
    }

    // 2. Curvature Arcs & Rings
    const visibleCircles = geom.displayCircles || geom.circles;
    if (showCirclesSwitch.value && visibleCircles.length > 0) {
      const defsArcs = [];
      for (const c of visibleCircles) {
        defsArcs.push(PolyCurveNodeDefinition.create(makeSmoothCirclePoly(c.cx, c.cy, c.r), noFill, outlineStroke, lsdOutline, noFill));
      }
      subContainers.push({ name: "2. Curvature Arcs & Rings", defs: defsArcs });
    }

    // 3. Construction Gridlines
    if (showGridSwitch.value) {
      const defs = [];
      const gridMode = gridModeCombo.selectedIndex;

      // MODO RADIAL (SÓ ATIVADO SE FOR UM ARRANJO RADIAL COMPROVADO)
      if (gridMode === 1 && geom.isRadialArray) {
        const innerPetals = geom.innerBand;
        const outerPetals = geom.outerBand;
        const minR = innerPetals.reduce((m, p) => Math.min(m, p.rIn), Infinity);
        const centerVoidLimit = Math.max(15.0, minR * 0.72);

        // A. Linhas Radiais Independentes (Sem fusão, sem choque)
        for (const petal of geom.petalData) {
          const isOuter = (outerPetals.indexOf(petal) !== -1);

          for (const edge of petal.radialEdges) {
            let pStart = { x: edge.pIn.x, y: edge.pIn.y };
            let pEnd = { x: edge.pOut.x, y: edge.pOut.y };

            if (isOuter) {
              let dToInner = Infinity;
              for (const ip of innerPetals) {
                for (const ipt of ip.pts) {
                  dToInner = Math.min(dToInner, dist(edge.pIn, ipt));
                }
              }
              const backSpan = (dToInner < 10.0) ? 0 : Math.min(edge.len * 0.18, Math.max(0, dToInner - 8.0));
              pStart = {
                x: edge.pIn.x - edge.dir.x * backSpan,
                y: edge.pIn.y - edge.dir.y * backSpan
              };
              pEnd = intersectRayWithRect(edge.pOut, edge.dir, constructionBounds);
            } else {
              const curDist = dist(edge.pIn, center);
              const maxBack = Math.max(0, curDist - centerVoidLimit);
              const backSpan = Math.min(edge.len * 0.18, maxBack);
              pStart = {
                x: edge.pIn.x - edge.dir.x * backSpan,
                y: edge.pIn.y - edge.dir.y * backSpan
              };

              let dToOuter = Infinity;
              if (outerPetals.length > 0) {
                for (const op of outerPetals) {
                  for (const opt of op.pts) {
                    dToOuter = Math.min(dToOuter, dist(edge.pOut, opt));
                  }
                }
              }
              const forwardSpan = isFinite(dToOuter) ? Math.max(0, Math.min(22.0, dToOuter - 8.0)) : Math.min(22.0, edge.len * 0.6);
              pEnd = {
                x: edge.pOut.x + edge.dir.x * forwardSpan,
                y: edge.pOut.y + edge.dir.y * forwardSpan
              };
            }

            defs.push(PolyCurveNodeDefinition.create(makeLinePoly(pStart.x, pStart.y, pEnd.x, pEnd.y), noFill, gridStroke, lsdGrid, noFill));
          }

          // B. Guias de Corte Transversal nas Extremidades (Com expansão generosa e mesmo estilo da grelha!)
          for (const cap of petal.capEdges) {
            // Expansão visível de 12 a 24px (proporcional à pétala)
            const desiredSpan = clamp(cap.len * 0.55, 12.0, 24.0);
            let deltaA = desiredSpan;
            let deltaB = desiredSpan;

            // Proteção analítica: se outra pétala estiver próxima, limita para não invadir o corpo vizinho
            for (const otherPetal of geom.petalData) {
              if (otherPetal !== petal) {
                for (const opt of otherPetal.pts) {
                  const dA = dist(cap.p1, opt);
                  if (dA < desiredSpan + 4.0) deltaA = Math.min(deltaA, Math.max(0, dA - 6.0));

                  const dB = dist(cap.p2, opt);
                  if (dB < desiredSpan + 4.0) deltaB = Math.min(deltaB, Math.max(0, dB - 6.0));
                }
              }
            }

            const cStart = { x: cap.p1.x - cap.dir.x * deltaA, y: cap.p1.y - cap.dir.y * deltaA };
            const cEnd = { x: cap.p2.x + cap.dir.x * deltaB, y: cap.p2.y + cap.dir.y * deltaB };
            // Compartilha a mesma cor e espessura da grelha (gridStroke e lsdGrid)
            defs.push(PolyCurveNodeDefinition.create(makeLinePoly(cStart.x, cStart.y, cEnd.x, cEnd.y), noFill, gridStroke, lsdGrid, noFill));
          }
        }
      } else {
        // GENERAL CONSTRUCTION ENGINE
        // Uses the complete geometric data, not the visually filtered anchor list.
        // This keeps guide generation independent from marker collision controls.
        const candidates = [];
        const gridOrigin = exactCenter;
        const alignmentPoints = [];

        for (const a of geom.anchors) {
          alignmentPoints.push({ x: a.x, y: a.y, importance: a.importance || a.priority || 30 });
        }
        for (const l of geom.landmarks) {
          alignmentPoints.push({ x: l.x, y: l.y, importance: l.importance || (l.type === "extrema" ? 70 : 45) });
        }

        const preciseAngle = initialPreciseAngle;
        const alignmentTolerance = Math.max(1.0, mergeDistCtrl.value);
        const directionFamilies = (geom.directionFamilies || []).slice(0, 4);

        if (gridMode === 0) {
          // Smart Adaptive combines independent structural-edge and Bézier-tangent
          // families. A curved path can contribute valid directions without one
          // dominant straight segment suppressing all other orientations.
          const selectedFamilies = directionFamilies.slice(0, 3);
          if (selectedFamilies.length) {
            selectedFamilies.forEach((family, index) => {
              const familyBoost = Math.min(10, (family.confidence || 0) * 10);
              addAlignmentLineCandidates(
                alignmentPoints, gridOrigin, family.angle, alignmentTolerance,
                candidates, 30 + familyBoost - index * 2.5, "direction-family-alignment"
              );
              // The perpendicular is retained only when supported by the actual
              // projected geometry; its lower ranking prevents artificial grids.
              addAlignmentLineCandidates(
                alignmentPoints, gridOrigin, family.angle + Math.PI / 2, alignmentTolerance,
                candidates, 25 + familyBoost - index * 2.5, "direction-family-perpendicular"
              );
            });
          } else {
            addAlignmentLineCandidates(alignmentPoints, gridOrigin, preciseAngle, alignmentTolerance, candidates, 32, "dominant-alignment");
            addAlignmentLineCandidates(alignmentPoints, gridOrigin, preciseAngle + Math.PI / 2, alignmentTolerance, candidates, 29, "perpendicular-alignment");
          }

          // Preserve substantial straight edges. Very short edges often belong
          // to local contour details and should not become full-frame diagonals.
          const minGuideEdge = Math.max(6, Math.hypot(exactBounds.width, exactBounds.height) * 0.045);
          for (const seg of geom.straightSegments) {
            if (dist(seg.p1, seg.p2) < minGuideEdge) continue;
            candidates.push({ p1: seg.p1, p2: seg.p2, angle: seg.angle, importance: 82, support: 1, source: "structural-edge" });
          }
        } else if (gridMode === 2) {
          // Orthogonal grid: cluster all real nodes and curve landmarks, not only
          // the anchors currently visible in the marker layer.
          addAlignmentLineCandidates(alignmentPoints, gridOrigin, 0, alignmentTolerance, candidates, 38, "horizontal-alignment");
          addAlignmentLineCandidates(alignmentPoints, gridOrigin, Math.PI / 2, alignmentTolerance, candidates, 38, "vertical-alignment");
        } else {
          // Structural Edges: keep actual straight segments and avoid fabricating
          // diagonal chords across curved portions of the logo.
          for (const seg of geom.straightSegments) {
            candidates.push({ p1: seg.p1, p2: seg.p2, angle: seg.angle, importance: 86, support: 1, source: "structural-edge" });
          }
          // Repeated endpoint alignments remain useful even in edge-focused mode.
          // Use up to two genuinely supported directions, not an arbitrary chord.
          if (directionFamilies.length) {
            directionFamilies.slice(0, 2).forEach((family, index) => {
              addAlignmentLineCandidates(
                alignmentPoints, gridOrigin, family.angle, alignmentTolerance,
                candidates, 28 - index * 3, "edge-family-alignment"
              );
            });
          } else {
            addAlignmentLineCandidates(alignmentPoints, gridOrigin, preciseAngle, alignmentTolerance, candidates, 24, "edge-alignment");
          }
        }

        // Local Bézier tangents are opt-in. They are not global construction axes
        // by default: otherwise every curve extremum can project an arbitrary
        // full-frame line and overwhelm the structural grid.
        const tangentMode = tangentSourceCombo.selectedIndex;
        if (tangentMode >= 1) {
          addBezierTangentCandidates(polyCurve, geom.handles, candidates, tangentMode === 2);
        }

        // The frame is finite; centre axes follow the selected reach boundary.
        // Diagonals are only proposed when the exact bounds are nearly square.
        addBoundingBoxGuides(exactBounds, candidates, true);

        // Curvature centres create useful cross-axes, while the actual circles
        // remain in their independent layer.
        if ((showCirclesSwitch.value || showModulesSwitch.value) && geom.circleFamilies && geom.circleFamilies.length > 0) {
          addCircleFamilyConstructionCandidates(geom.circleFamilies, candidates);
        }

        if (showSymmetrySwitch.value && initialGridSymmetry.score >= 0.70) {
          candidates.push({
            p1: exactCenter,
            angle: initialGridSymmetry.axis,
            importance: 100,
            source: "symmetry-axis"
          });
        }

        if (showModulesSwitch.value && geom.modules && Array.isArray(geom.modules.axes)) {
          // Only high-confidence systems are promoted to construction modules.
          // Their phase comes from the measured anchor/landmark positions.
          for (const axis of geom.modules.axes.slice(0, 2)) {
            createModuleGridCandidates(axis, exactBounds, exactCenter, candidates, alignmentTolerance);
          }
        }

        const cleanLines = buildCollisionSafeLines(
          candidates,
          { anchors: geom.anchors, handles: geom.handles, points: geom.landmarks },
          mergeDistCtrl.value,
          exactBounds
        );

        // Keep the strongest and best-supported guides; duplicate filtering is
        // geometric, not based on how many anchors a valid line happens to cross.
        // Merge tolerance also provides a restrained detail control: larger
        // values remove near-duplicate candidates and lower the guide budget.
        const detailFactor = clamp(1.18 - mergeDistCtrl.value * 0.0062, 0.56, 1.12);
        const baseGuideBudget = gridMode === 2 ? 28 : (gridMode === 3 ? 22 : 20);
        const guideBudget = Math.max(10, Math.round(baseGuideBudget * detailFactor));
        for (const line of cleanLines.slice(0, guideBudget)) {
          const clipBounds = (line.source === "bounding-box-edge" || line.source === "bounding-box-diagonal")
            ? exactBounds
            : constructionBounds;
          const ext = extendLineToRect(line, clipBounds);
          if (!ext || dist(ext.p1, ext.p2) < 1.0) continue;
          appendStyledGridLine(defs, line, ext, gridStrokeStyles, noFill);
        }


      }
      if (defs.length) subContainers.push({ name: "3. Construction Gridlines", defs: defs });
    }

    // 4. Geometric Landmarks
    // Only derived curve events are shown here. Native path vertices remain
    // exclusively in Anchor Nodes, avoiding a second marker over the same node.
    if (showLandmarksSwitch.value) {
      const defs = [];
      const baseLandmarkR = Math.max(1.0, landmarkSizeCtrl.value / 2);
      for (const l of geom.landmarks) {
        if (l.type !== "extrema" && l.type !== "cusp" && l.type !== "stationary") continue;
        if (geom.anchors.some(a => dist(a, l) <= landmarkCoincidenceTolerance)) continue;
        const markerRadius = l.type === "cusp" ? baseLandmarkR * 1.25 : baseLandmarkR;
        defs.push(PolyCurveNodeDefinition.create(makeSmoothCirclePoly(l.x, l.y, markerRadius), landmarkFillDesc, landmarkStrokeDesc, lsdNode, noFill));
      }
      if (defs.length) subContainers.push({ name: "4. Geometric Landmarks", defs: defs });
    }

    // 5. Inflection Points
    if (showInflectionSwitch.value) {
      const baseInflectR = Math.max(1.0, handleSizeCtrl.value * 0.35);
      const defs = geom.landmarks.filter(l => l.type === "inflection").map(l => PolyCurveNodeDefinition.create(makeSmoothCirclePoly(l.x, l.y, baseInflectR), landmarkFillDesc, landmarkStrokeDesc, lsdNode, noFill));
      if (defs.length) subContainers.push({ name: "5. Inflection Points", defs: defs });
    }

    // 6 & 7. Bezier Handles (Stems & Dots)
    if (showHandlesSwitch.value && visualHandles.length > 0) {
      const defsStems = [], defsDots = [];
      for (const h of visualHandles) {
        const rawDx = h.handle.x - h.anchor.x, rawDy = h.handle.y - h.anchor.y;
        const d = Math.hypot(rawDx, rawDy);
        if (d <= EPS) continue;

        const ux = rawDx / d, uy = rawDy / d;
        const dotRadius = Math.max(0.5, h.dotRadius);
        const projectedLength = Math.max(d, d * stemMultiplier);
        const projectedEndX = h.anchor.x + ux * projectedLength;
        const projectedEndY = h.anchor.y + uy * projectedLength;

        // Segmento principal: termina antes do círculo na posição real do handle.
        if (d > dotRadius + 1) {
          defsStems.push(PolyCurveNodeDefinition.create(
            makeLinePoly(
              h.anchor.x, h.anchor.y,
              h.handle.x - ux * dotRadius,
              h.handle.y - uy * dotRadius
            ),
            noFill, stemStroke, lsdNode, noFill
          ));
        }

        // Projeções >1x prolongam somente a haste após o ponto; nunca deslocam
        // o marcador da coordenada de controlo Bézier verdadeira.
        if (projectedLength > d + dotRadius + 1 && d > dotRadius + 1) {
          defsStems.push(PolyCurveNodeDefinition.create(
            makeLinePoly(
              h.handle.x + ux * dotRadius,
              h.handle.y + uy * dotRadius,
              projectedEndX,
              projectedEndY
            ),
            noFill, stemStroke, lsdNode, noFill
          ));
        }

        defsDots.push(PolyCurveNodeDefinition.create(
          makeSmoothCirclePoly(h.handle.x, h.handle.y, dotRadius),
          dotFillDesc, dotStrokeDesc, lsdNode, noFill
        ));
      }
      if (defsStems.length) subContainers.push({ name: "6. Handle Stems", defs: defsStems });
      if (defsDots.length) subContainers.push({ name: "7. Handle Dots", defs: defsDots });
    }

    // 8. Anchor Nodes
    if (showAnchorsSwitch.value && displayAnchors.length > 0) {
      subContainers.push({
        name: "8. Anchor Nodes",
        defs: displayAnchors.map(a => PolyCurveNodeDefinition.create(makeSquarePoly(a.x, a.y, a.halfSize), anchorFillDesc, anchorStrokeDesc, lsdNode, noFill))
      });
    }

    return { subContainers: subContainers };
  }

  function render(isPreview) {
    doc.executeCommand(DocumentCommand.createClearPreviews());
    const structure = buildGridStructure();
    if (!structure || structure.subContainers.length === 0) return;
    const addBuilder = AddChildNodesCommandBuilder.create();
    addBuilder.setInsertionTargetSelection(Selection.create(doc, primaryNode));
    addBuilder.setInsertionMode(InsertionMode.Top);
    structure.subContainers.forEach(sc => sc.defs.forEach(def => addBuilder.addNode(def)));
    const cmd = addBuilder.createCommand(false, NodeChildType.Main);
    doc.executeCommand(cmd, isPreview);
  }

  // Event Listeners Reativos para Live Preview
  [
    gridModeCombo, nodeDisplayCombo, reachModeCombo, tangentSourceCombo, anchorStyleCombo,
    handleStyleCombo, landmarkStyleCombo, stemScaleCombo, handleScalingCombo
  ].forEach(c => {
    try { c.setOnValueChangedHandler(() => render(true)); } catch (e) {}
  });

  [
    showOverlaySwitch, showOutlineSwitch, showCirclesSwitch, showGridSwitch, showHandlesSwitch,
    showAnchorsSwitch, adaptiveScaleSwitch, showSymmetrySwitch,
    showModulesSwitch, showLandmarksSwitch, showInflectionSwitch
  ].forEach(c => {
    try { c.setOnValueChangedHandler(() => render(true)); } catch (e) {}
  });

  [
    overlayOpacityCtrl, minNodeGapCtrl, gridReachCtrl, mergeDistCtrl, anchorSizeCtrl,
    handleSizeCtrl, landmarkSizeCtrl, outlineWidthCtrl, gridWidthCtrl, nodeStrokeWidthCtrl
  ].forEach(c => {
    try { c.setOnValueChangedHandler(() => render(true)); } catch (e) {}
  });

  [
    outlineColorPicker, gridColorPicker, stemColorPicker, handleDotFillPicker,
    anchorFillPicker, landmarkFillPicker, nodeBorderPicker, landmarkBorderPicker
  ].forEach(c => {
    try { c.setOnValueChangedHandler(() => render(true)); } catch (e) {}
  });

  render(true);
  const res = dlg.runModal();
  doc.executeCommand(DocumentCommand.createClearPreviews());

  if (isDialogOk(res)) {
    const structure = buildGridStructure();
    if (structure && structure.subContainers.length > 0) {
      const parentBuilder = AddChildNodesCommandBuilder.create();
      parentBuilder.setInsertionTargetSelection(Selection.create(doc, primaryNode));
      parentBuilder.setInsertionMode(InsertionMode.Top);
      parentBuilder.addContainerNode(ContainerNodeDefinition.create("Logo Construction Grid"));
      const parentCmd = parentBuilder.createCommand(false, NodeChildType.Main);
      doc.executeCommand(parentCmd);

      const newParentNodes = parentCmd.newNodes
        ? (Array.isArray(parentCmd.newNodes) ? parentCmd.newNodes : (parentCmd.newNodes.toArray ? parentCmd.newNodes.toArray() : Array.from(parentCmd.newNodes)))
        : [];
      const parentContainerNode = newParentNodes[0] || null;

      if (parentContainerNode) {
        for (const sc of structure.subContainers) {
          if (!sc.defs || !sc.defs.length) continue;
          const subBuilder = AddChildNodesCommandBuilder.create();
          subBuilder.setInsertionTarget(parentContainerNode);
          subBuilder.addContainerNode(ContainerNodeDefinition.create(sc.name));
          const subCmd = subBuilder.createCommand(false, NodeChildType.Main);
          doc.executeCommand(subCmd);

          const newSubNodes = subCmd.newNodes
            ? (Array.isArray(subCmd.newNodes) ? subCmd.newNodes : (subCmd.newNodes.toArray ? subCmd.newNodes.toArray() : Array.from(subCmd.newNodes)))
            : [];
          const subContainerNode = newSubNodes[0] || null;
          if (subContainerNode) {
            const defsBuilder = AddChildNodesCommandBuilder.create();
            defsBuilder.setInsertionTarget(subContainerNode);
            sc.defs.forEach(def => defsBuilder.addNode(def));
            const defsCmd = defsBuilder.createCommand(false, NodeChildType.Main);
            doc.executeCommand(defsCmd);
          }
        }
      }

      // Oculta o objeto original por padrão
      for (const it of rawSel) {
        try { doc.executeCommand(DocumentCommand.createSetVisibility(it.selfSelection, false)); } catch (e) {}
      }
    }
  }
}

main();