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

function getDirectNodeChildren(node) {
  if (!node) return [];

  // Prefer a collection API when the node type exposes it.
  try {
    const children = toArray(node.children);
    if (children.length) return children.filter(Boolean);
  } catch (e) {}

  // Affinity DOM nodes also expose their hierarchy as a linked sibling chain.
  // This fallback is important for GroupNode and nested group selections.
  const result = [];
  const visited = new Set();
  try {
    let child = node.firstChild || null;
    while (child && !visited.has(child)) {
      visited.add(child);
      result.push(child);
      child = child.nextSibling || null;
    }
  } catch (e) {}

  return result;
}

function extractCompositePolyCurve(rootNodes) {
  const masterPoly = PolyCurve.create();
  const components = [];
  const groups = [];
  let totalCurveCount = 0;
  let maxDepth = 0;
  const visitedNodes = new Set();

  function getNodeLabel(node, fallback) {
    try {
      const value = node && (node.name || node.label || node.displayName);
      if (typeof value === "string" && value.trim()) return value.trim();
    } catch (e) {}
    return fallback;
  }

  function traverse(node, depth, parentGroupIds) {
    if (!node || isEmbeddedDocumentNode(node) || visitedNodes.has(node)) return;
    visitedNodes.add(node);
    maxDepth = Math.max(maxDepth, depth);

    const children = getDirectNodeChildren(node);
    let nextParents = parentGroupIds;

    if (children.length > 0) {
      const groupId = groups.length;
      groups.push({
        id: groupId,
        label: getNodeLabel(node, "Group " + (groupId + 1)),
        depth,
        parentGroupIds: parentGroupIds.slice(),
        childCount: children.length
      });
      nextParents = parentGroupIds.concat(groupId);
    }

    // Do not read aggregate geometry from a container: its child vectors are
    // traversed individually, preventing the same paths from being added twice.
    if (children.length === 0) {
      const directPc = extractPolyCurvesFromSingleNode(node);
      if (directPc && directPc.curveCount > 0) {
        const curveStart = totalCurveCount;
        for (let c = 0; c < directPc.curveCount; c++) {
          masterPoly.addCurve(directPc.at(c).clone());
          totalCurveCount++;
        }

        let bounds = null;
        try { bounds = getExactCurveBounds(directPc); } catch (e) {}
        components.push({
          id: components.length,
          label: getNodeLabel(node, "Component " + (components.length + 1)),
          depth,
          parentGroupIds: parentGroupIds.slice(),
          curveStart,
          curveCount: directPc.curveCount,
          bounds
        });
      }
    }

    for (const child of children) traverse(child, depth + 1, nextParents);
  }

  for (const node of (rootNodes || [])) traverse(node, 0, []);
  if (totalCurveCount === 0) return null;
  return {
    polyCurve: masterPoly,
    components,
    groups,
    componentCount: components.length,
    groupCount: groups.length,
    totalCurveCount,
    maxDepth
  };
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

  if (line.finiteSegment && line.p2) {
    const sx = line.p1.x, sy = line.p1.y;
    const dxSegment = line.p2.x - sx, dySegment = line.p2.y - sy;
    let t0 = 0, t1 = 1;
    const p = [-dxSegment, dxSegment, -dySegment, dySegment];
    const q = [sx - x1, x2 - sx, sy - y1, y2 - sy];
    for (let i = 0; i < 4; i++) {
      if (Math.abs(p[i]) <= EPS) {
        if (q[i] < 0) return null;
      } else {
        const ratio = q[i] / p[i];
        if (p[i] < 0) t0 = Math.max(t0, ratio);
        else t1 = Math.min(t1, ratio);
        if (t0 > t1) return null;
      }
    }
    return {
      p1: { x: sx + t0 * dxSegment, y: sy + t0 * dySegment },
      p2: { x: sx + t1 * dxSegment, y: sy + t1 * dySegment }
    };
  }
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
  const cellSize = Math.max(Number.EPSILON * 100, searchRadius || 1);
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
  // Fit in normalized local coordinates. This keeps the solver stable for both
  // tiny vector details and large document-space curves.
  const localScale = Math.max(
    dist(b.start, b.c1), dist(b.c1, b.c2), dist(b.c2, b.end), dist(b.start, b.end)
  );
  if (!Number.isFinite(localScale) || localScale <= Number.EPSILON * 100) return null;

  const FIT_SAMPLES = 11;
  const points = [];
  let meanX = 0, meanY = 0;
  for (let i = 0; i < FIT_SAMPLES; i++) {
    const point = cubicPoint(b, i / (FIT_SAMPLES - 1));
    points.push(point);
    meanX += point.x;
    meanY += point.y;
  }
  meanX /= FIT_SAMPLES;
  meanY /= FIT_SAMPLES;

  let Suu = 0, Svv = 0, Suv = 0;
  let Suuu = 0, Svvv = 0, Suvv = 0, Svuu = 0;
  for (const point of points) {
    const u = (point.x - meanX) / localScale;
    const v = (point.y - meanY) / localScale;
    const u2 = u * u, v2 = v * v;
    Suu += u2;
    Svv += v2;
    Suv += u * v;
    Suuu += u2 * u;
    Svvv += v2 * v;
    Suvv += u * v2;
    Svuu += v * u2;
  }

  const determinant = Suu * Svv - Suv * Suv;
  if (!Number.isFinite(determinant) || Math.abs(determinant) <= 1e-12) return null;

  const rhs1 = 0.5 * (Suuu + Suvv);
  const rhs2 = 0.5 * (Svvv + Svuu);
  const centreU = (rhs1 * Svv - rhs2 * Suv) / determinant;
  const centreV = (Suu * rhs2 - Suv * rhs1) / determinant;
  const radiusNormalised = Math.sqrt(
    centreU * centreU + centreV * centreV + (Suu + Svv) / FIT_SAMPLES
  );
  const cx = meanX + centreU * localScale;
  const cy = meanY + centreV * localScale;
  const radius = radiusNormalised * localScale;

  // A very large radius relative to this segment is effectively a straight line;
  // a very small one is usually a cusp or a degenerate control polygon.
  if (!Number.isFinite(radius) || radius < localScale * 0.02 || radius > localScale * 100) return null;

  // Validate the complete cubic, not only the sparse points used by the fit.
  // This catches inflections and variable-curvature segments that happen to
  // look circular at seven isolated samples.
  const VALIDATION_SAMPLES = 49;
  const centre = { x: cx, y: cy };
  let maxDeviation = 0;
  let maxTangentError = 0;
  let sweep = 0;
  let previousAngle = null;
  let previousTurnSign = 0;
  let directionChanges = 0;

  for (let i = 0; i < VALIDATION_SAMPLES; i++) {
    const t = i / (VALIDATION_SAMPLES - 1);
    const point = cubicPoint(b, t);
    const radialX = point.x - cx;
    const radialY = point.y - cy;
    const radialLength = Math.hypot(radialX, radialY);
    if (!Number.isFinite(radialLength) || radialLength <= Number.EPSILON * 100) return null;

    maxDeviation = Math.max(maxDeviation, Math.abs(radialLength - radius));

    const angle = Math.atan2(radialY, radialX);
    if (previousAngle !== null) {
      let delta = angle - previousAngle;
      while (delta > Math.PI) delta -= Math.PI * 2;
      while (delta < -Math.PI) delta += Math.PI * 2;
      sweep += delta;
      if (Math.abs(delta) > 0.02 * DEG) {
        const turnSign = delta > 0 ? 1 : -1;
        if (previousTurnSign && turnSign !== previousTurnSign) directionChanges++;
        previousTurnSign = turnSign;
      }
    }
    previousAngle = angle;

    const tangent = cubicDerivative(b, t);
    const tangentLength = Math.hypot(tangent.x, tangent.y);
    if (tangentLength > localScale * 1e-9) {
      const radialAlignment = Math.abs(
        (tangent.x * radialX + tangent.y * radialY) / (tangentLength * radialLength)
      );
      maxTangentError = Math.max(maxTangentError, radialAlignment);
    }
  }

  const absoluteSweep = Math.abs(sweep);
  if (absoluteSweep < 6 * DEG || absoluteSweep > 200 * DEG || directionChanges > 0) return null;

  const allowedDeviation = Math.max(localScale * 0.001, radius * 0.008);
  if (maxDeviation > allowedDeviation) return null;
  if (maxTangentError > Math.sin(10 * DEG)) return null;

  const confidence = clamp(1 - maxDeviation / allowedDeviation, 0, 1);
  return {
    cx, cy, r: radius, confidence,
    arcSweep: absoluteSweep,
    maxDeviation,
    maxTangentError
  };
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
      componentIds: [],
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
    if (Number.isInteger(r.componentId) && anchor.componentIds.indexOf(r.componentId) < 0) anchor.componentIds.push(r.componentId);
    if (Number.isInteger(r.segmentIndex)) anchor.sourceSegments.push({ contour: r.contourIndex, segment: r.segmentIndex, componentId: r.componentId });
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
  const validAnchors=(anchors||[]).filter(p=>p&&Number.isFinite(p.x)&&Number.isFinite(p.y));
  if(validAnchors.length<3)return{score:0,axis:angle,perpendicular:angle+Math.PI/2};

  const ca=Math.cos(angle),sa=Math.sin(angle);
  const points=validAnchors.map(p=>({u:p.x*ca+p.y*sa,v:-p.x*sa+p.y*ca}));
  const uMin=Math.min.apply(null,points.map(p=>p.u)),uMax=Math.max.apply(null,points.map(p=>p.u));
  const vMin=Math.min.apply(null,points.map(p=>p.v)),vMax=Math.max.apply(null,points.map(p=>p.v));
  const uMid=(uMin+uMax)/2,vMid=(vMin+vMax)/2;
  const spanU=uMax-uMin,spanV=vMax-vMin;
  const diagonal=Math.max(Number.EPSILON*100,Math.hypot(spanU,spanV));
  const minorDimension=Math.max(diagonal*0.04,Math.min(spanU,spanV));
  const matchTolerance=Math.max(diagonal*0.0005,minorDimension*0.03);
  const cellSize=Math.max(matchTolerance,Number.EPSILON*100);
  const buckets=new Map();
  const key=(x,y)=>x+","+y;

  for(const p of points){
    const gx=Math.floor(p.u/cellSize),gy=Math.floor(p.v/cellSize);
    const k=key(gx,gy);
    if(!buckets.has(k))buckets.set(k,[]);
    buckets.get(k).push(p);
  }

  function hasMirroredMatch(target){
    const gx=Math.floor(target.u/cellSize),gy=Math.floor(target.v/cellSize);
    for(let dx=-1;dx<=1;dx++){
      for(let dy=-1;dy<=1;dy++){
        const bucket=buckets.get(key(gx+dx,gy+dy));
        if(!bucket)continue;
        for(const q of bucket){
          if(Math.hypot(target.u-q.u,target.v-q.v)<=matchTolerance)return true;
        }
      }
    }
    return false;
  }

  function mirrorScore(useU){
    let matched=0;
    for(const p of points){
      const target=useU
        ? {u:2*uMid-p.u,v:p.v}
        : {u:p.u,v:2*vMid-p.v};
      if(hasMirroredMatch(target))matched++;
    }
    return matched/points.length;
  }

  const longitudinal=mirrorScore(false),transverse=mirrorScore(true);
  return{
    longitudinal,transverse,
    score:Math.max(longitudinal,transverse),
    axis:longitudinal>=transverse?angle:angle+Math.PI/2,
    perpendicular:longitudinal>=transverse?angle+Math.PI/2:angle
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
function analyzeSmartGeometry(polyCurve, baseAnchorSize, baseHandleSize, componentModel) {
  const rawHandles = [], straightSegments = [], directionSegments = [], rawCircles = [], landmarkRecords = [], topologyRecords = [];
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  let realCurveSegments = 0;
  let straightSegmentTotal = 0, contourSegmentTotal = 0, openContourTotal = 0;
  const componentMetrics = ((componentModel && componentModel.components) || []).map(component => ({
    id: component.id, label: component.label, depth: component.depth,
    parentGroupIds: component.parentGroupIds || [], curveStart: component.curveStart,
    curveCount: component.curveCount, bounds: component.bounds || null,
    contourCount: 0, closedContourCount: 0, openContourCount: 0,
    straightSegmentCount: 0, curveSegmentCount: 0, anchorCount: 0, handleCount: 0
  }));
  function componentForCurve(curveIndex) {
    for (const component of componentMetrics) {
      if (curveIndex >= component.curveStart &&
          curveIndex < component.curveStart + component.curveCount) return component.id;
    }
    return -1;
  }

  function updateBounds(p) {
    minX = Math.min(minX, p.x); minY = Math.min(minY, p.y);
    maxX = Math.max(maxX, p.x); maxY = Math.max(maxY, p.y);
  }

  const closedPetals = [];
  let closedContourTotal = 0;

  for (let c = 0; c < polyCurve.curveCount; c++) {
    const curve = polyCurve.at(c);
    const componentId = componentForCurve(c);
    const componentMetric = componentMetrics.find(item => item.id === componentId) || null;
    const beziers = collectBeziers(curve);
    const closedContour = isCurveClosed(curve, beziers);
    if (componentMetric) {
      componentMetric.contourCount++;
      if (closedContour) componentMetric.closedContourCount++;
      else componentMetric.openContourCount++;
    }
    if (closedContour) closedContourTotal++;
    else openContourTotal++;
    const firstContourPoint = beziers.length ? beziers[0].start : null;
    const lastContourPoint = beziers.length ? beziers[beziers.length - 1].end : null;
    const contourSeamLength = firstContourPoint && lastContourPoint ? dist(firstContourPoint, lastContourPoint) : Infinity;
    const contourSeamTolerance = curveClosureTolerance(beziers);
    const hasImplicitClosingEdge = closedContour && contourSeamLength > contourSeamTolerance;
    const contourPoints = [];
    const contourEdges = [];
    let contourScale = 1;

    for (let bIdx = 0; bIdx < beziers.length; bIdx++) {
      contourSegmentTotal++;
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

      // Circle fitting only runs on genuinely curved Bézier segments. The fit
      // itself uses scale-relative geometry and dense validation, so an absolute
      // 0.45-unit chord threshold cannot suppress small but real circular arcs.
      if (!isSegmentStraight) {
        const circleFit = fitCircleToBezier(b);
        if (circleFit) {
          circleFit.componentId = componentId;
          circleFit.contourIndex = c;
          circleFit.segmentIndex = bIdx;
          circleFit.contourSegmentCount = beziers.length;
          circleFit.closedContour = closedContour;
          circleFit.circleScopeKey = componentMetric && componentMetric.parentGroupIds &&
            componentMetric.parentGroupIds.length
            ? "group:" + componentMetric.parentGroupIds[0]
            : "component:" + componentId;
          rawCircles.push(circleFit);
        }
      }

      if (isSegmentStraight) {
        straightSegmentTotal++;
        if (componentMetric) componentMetric.straightSegmentCount++;
        if (chord >= Math.max(controlScale * 1e-3, Number.EPSILON)) {
          const angle = canonicalLineAngle(Math.atan2(b.end.y - b.start.y, b.end.x - b.start.x));
          const seg = { p1: b.start, p2: b.end, angle: angle, length: chord, importance: 85, componentId };
          straightSegments.push(seg);
          directionSegments.push({ p1: b.start, p2: b.end, componentId });
          contourEdges.push(seg);
        }
      } else {
        realCurveSegments++;
        if (componentMetric) componentMetric.curveSegmentCount++;
        const mid = cubicPoint(b, 0.5);
        directionSegments.push({ p1: b.start, p2: mid });
        directionSegments.push({ p1: mid, p2: b.end });

        const handleEpsilon = Math.max(1e-9, controlScale * 1e-9);
        if (dC1 > handleEpsilon) {
          rawHandles.push({
            anchor: b.start, handle: b.c1, length: dC1,
            importance: Math.min(100, 35 + dC1 * 0.5),
            contourIndex: c, segmentIndex: bIdx, componentId, controlSide: "outgoing",
            anchorTopologyKey: c + ":vertex:" + bIdx,
            closedContour
          });
        }
        if (dC2 > handleEpsilon) {
          rawHandles.push({
            anchor: b.end, handle: b.c2, length: dC2,
            importance: Math.min(100, 35 + dC2 * 0.5),
            contourIndex: c, segmentIndex: bIdx, componentId, controlSide: "incoming",
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
            contourIndex: c, componentId, segmentIndex: bIdx, t,
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
            contourIndex: c, componentId, segmentIndex: bIdx, t,
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
              contourIndex: c, componentId, segmentIndex: bIdx, t,
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
        componentId,
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
        componentId,
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
          componentId,
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
          componentId,
          segmentIndex: -1,
          topologyKey: c + ":vertex:0"
        });

        // The implicit closing edge also contributes to direction analysis
        // and to polygonal/radial construction, but very short closures are
        // not promoted to visible straight-edge guides.
        if (seamLength >= contourScale * 5e-4) directionSegments.push({ p1: last, p2: first });
        if (seamLength >= contourScale * 1e-3) {
          const closure = {
            p1: last,
            p2: first,
            angle: canonicalLineAngle(seamAngle),
            length: seamLength,
            importance: 85,
            implicitClosure: true,
            componentId
          };
          straightSegments.push(closure);
          contourEdges.push(closure);
        }
      }
    }

    // Only truly closed contours feed the radial-petal analyser. Open paths
    // with three or more segments must not be mistaken for closed petals.
    if (closedContour && contourPoints.length >= 3) {
      closedPetals.push({ pts: contourPoints, edges: contourEdges, componentId });
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
  const objectScaleContext = createGeometryScaleContext(bounds);
  const featureLengthFloor = objectScaleContext.featureLength;
  const circleFeatureScale = Math.max(
    objectScaleContext.diagonal * 0.04,
    Math.min(Math.abs(bounds.width), Math.abs(bounds.height))
  );
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
      if (len < featureLengthFloor) continue;
      const ux = (pOut.x - pIn.x) / len;
      const uy = (pOut.y - pIn.y) / len;
      radialEdges.push({ pIn, pOut, len, dir: { x: ux, y: uy }, angle: canonicalLineAngle(Math.atan2(uy, ux)) });
    }

    // As 2 arestas curtas de fecho são transversais (cortes das pontas)
    for (const e of sortedEdges.slice(2, 4)) {
      const len = dist(e.p1, e.p2);
      if (len < featureLengthFloor) continue;
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
    const match = uniqueCircles.find(ex =>
      ex.componentId === c.componentId &&
      dist(ex, c) < Math.max(3.0, c.r * 0.04) &&
      Math.abs(ex.r - c.r) < Math.max(2.5, c.r * 0.035)
    );
    if (match) {
      const samples = match.samples || 1;
      const nextSamples = samples + 1;
      match.cx = (match.cx * samples + c.cx) / nextSamples;
      match.cy = (match.cy * samples + c.cy) / nextSamples;
      match.r = (match.r * samples + c.r) / nextSamples;
      match.confidence = Math.max(match.confidence || 0, c.confidence || 0);
      match.samples = nextSamples;
    } else {
      uniqueCircles.push({
        cx: c.cx, cy: c.cy, r: c.r,
        confidence: c.confidence,
        samples: 1,
        componentId: c.componentId
      });
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
      if (g > maxGap && g > geometryScale.diagonal * 0.02) { maxGap = g; splitIdx = i; }
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
  const nearestAnchorDistances = calculateNearestDistances(sortedAnchors, Math.max(Number.EPSILON * 100, baseAnchorSize * 2.4));
  const adaptiveAnchors = sortedAnchors.map((a, i) => {
    const nearest = nearestAnchorDistances[i];
    const halfSize = nearest < baseAnchorSize * 2.4 ? Math.max(baseHalf * 0.12, Math.min(baseHalf, nearest * 0.32)) : baseHalf;
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
    const minDotR = Math.max(Number.EPSILON * 100, baseDotR * 0.25);
    const calculatedDotR = localClearance < baseHandleSize * 2.2
      ? Math.max(minDotR, Math.min(baseDotR, localClearance * 0.22))
      : baseDotR;

    adaptiveHandles.push({
      anchor: h.anchor,
      handle: h.handle,
      componentId: h.componentId,
      dotRadius: calculatedDotR,
      baseLength: h.length,
      importance: h.importance,
      clearance: localClearance,
      priority: h.importance
    });
  }

  for (const component of componentMetrics) {
    component.anchorCount = adaptiveAnchors.filter(a => a.componentIds && a.componentIds.indexOf(component.id) !== -1).length;
    component.handleCount = adaptiveHandles.filter(h => h.componentId === component.id).length;
  }

  return {
    anchors: adaptiveAnchors,
    handles: adaptiveHandles,
    straightSegments: straightSegments,
    petalData: petalData,
    innerBand: innerBand,
    outerBand: outerBand,
    circles: uniqueCircles,
    rawCircleCandidates: rawCircles,
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
    openContourCount: openContourTotal,
    contourCount: polyCurve.curveCount,
    curveSegmentCount: realCurveSegments,
    straightSegmentCount: straightSegmentTotal,
    totalSegmentCount: contourSegmentTotal,
    radialPetalCandidateCount: closedPetals.length,
    featureCount: adaptiveAnchors.length + adaptiveHandles.length + uniqueCircles.length,
    componentMetrics
  };
}

function createGeometryScaleContext(bounds) {
  const width = Math.abs(Number(bounds && bounds.width) || 0);
  const height = Math.abs(Number(bounds && bounds.height) || 0);
  const diagonal = Math.max(Number.EPSILON * 100, Math.hypot(width, height));
  const minorFloor = diagonal * 0.04;
  // Geometric mean avoids letting a long wordmark's width dominate marker size.
  const reference = Math.sqrt(Math.max(width, minorFloor) * Math.max(height, minorFloor));
  return {
    width, height, diagonal, reference,
    scaleFactor: Math.max(1e-6, reference / 600)
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
    ? Math.max(Number.EPSILON * 100, Math.hypot(referenceBounds.width, referenceBounds.height))
    : 1000;
  const minorSpan = referenceBounds
    ? Math.max(Number.EPSILON * 100, Math.min(Math.abs(referenceBounds.width), Math.abs(referenceBounds.height)))
    : span;
  const positionTolerance = Math.max(
    Math.min(span * 0.0005, minorSpan * 0.001),
    Math.min((Number(mergeDist) || 0) * 0.08, minorSpan * 0.001)
  );
  const angleTolerance = Math.max(0.06 * DEG, Math.min(0.45 * DEG, Math.atan2(positionTolerance * 0.35, span)));
  const sorted = rawLines.slice().sort((a,b) => {
    const scoreA=(a.importance||0)+Math.min(20,(a.support||0)*2);
    const scoreB=(b.importance||0)+Math.min(20,(b.support||0)*2);
    return scoreB-scoreA;
  }).slice(0,1200);

  function projectedInterval(line, angle) {
    const ux=Math.cos(angle),uy=Math.sin(angle);
    const p2=line.p2&&Number.isFinite(line.p2.x)&&Number.isFinite(line.p2.y)
      ? line.p2
      : {x:line.p1.x+ux*Math.max(span,1000),y:line.p1.y+uy*Math.max(span,1000)};
    const a=line.p1.x*ux+line.p1.y*uy;
    const b=p2.x*ux+p2.y*uy;
    return {min:Math.min(a,b),max:Math.max(a,b)};
  }

  for (const line of sorted) {
    if(!line||!line.p1||!Number.isFinite(line.p1.x)||!Number.isFinite(line.p1.y))continue;
    let angle=line.angle;
    if(!Number.isFinite(angle)){
      if(!line.p2||!Number.isFinite(line.p2.x)||!Number.isFinite(line.p2.y))continue;
      angle=Math.atan2(line.p2.y-line.p1.y,line.p2.x-line.p1.x);
    }
    const rawAngle=angle;
    angle=canonicalLineAngle(angle);
    let normalizedOffset=Number.isFinite(line.offset)?line.offset:0;
    if(Math.cos(rawAngle-angle)<0)normalizedOffset=-normalizedOffset;
    const p2=line.p2&&Number.isFinite(line.p2.x)&&Number.isFinite(line.p2.y)
      ? {x:line.p2.x,y:line.p2.y}
      : {x:line.p1.x+Math.cos(angle)*Math.max(span,1000),y:line.p1.y+Math.sin(angle)*Math.max(span,1000)};
    const length=dist(line.p1,p2);
    if(!Number.isFinite(length)||length<=Number.EPSILON*100)continue;
    const finiteSegment=line.finiteSegment===true;
    const signedOffset=lineSignedNormalOffset({p1:line.p1,offset:normalizedOffset},angle);
    const scopeKey=line.scopeKey||"global";
    const currentInterval=projectedInterval({p1:line.p1,p2},angle);

    const duplicate=result.some(existing=>{
      if((existing.scopeKey||"global")!==scopeKey)return false;
      if(lineAngleDiff(existing.angle,angle)>angleTolerance)return false;
      if(Math.abs(lineSignedNormalOffset(existing,angle)-signedOffset)>positionTolerance)return false;

      // Keep disconnected collinear edges. A finite segment and a full inferred
      // alignment are also kept separate until the post-clipping overlap pass.
      if(finiteSegment || existing.finiteSegment) {
        // Keep finite path edges intact here. Their actual overlap is resolved
        // after clipping, when the rendered intervals are known.
        return false;
      }
      return true;
    });

    if(!duplicate){
      result.push({
        p1:{x:line.p1.x,y:line.p1.y},
        p2,
        angle,
        offset:normalizedOffset,
        finiteSegment,
        importance:line.importance||0,
        support:line.support||0,
        source:line.source||"geometry",
        scopeKey,
        componentId:Number.isInteger(line.componentId)?line.componentId:undefined,
        clipBounds:line.clipBounds||undefined
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
      if (Number.isInteger(line.componentId)) {
        const belongs = p.componentId === line.componentId ||
          (Array.isArray(p.componentIds) && p.componentIds.indexOf(line.componentId) !== -1);
        if (!belongs) continue;
      }
      const d = Math.abs(p.x * nx + p.y * ny - offset);
      const supportDiagonal = Math.hypot(
        referenceBounds && referenceBounds.width || 0,
        referenceBounds && referenceBounds.height || 0
      );
      const supportMinorSpan = referenceBounds
        ? Math.max(Number.EPSILON * 100, Math.min(Math.abs(referenceBounds.width), Math.abs(referenceBounds.height)))
        : supportDiagonal;
      const supportTolerance = Math.max(
        Math.min(supportDiagonal * 0.0015, supportMinorSpan * 0.025),
        Math.min(positionlessTolerance(mergeDist) * 0.18, supportMinorSpan * 0.025)
      );
      if (d <= supportTolerance) support++;
    }
    line.support = Math.max(line.support || 0, support);
    line._rank = (line.importance || 0) + Math.min(24, line.support * 2.5);
  }

  result.sort((a, b) => b._rank - a._rank);
  for (const line of result) delete line._rank;
  return result;
}

function mergeCoincidentRenderedLines(items, mergeDistance, referenceBounds) {
  const span = referenceBounds
    ? Math.max(Number.EPSILON * 100, Math.hypot(referenceBounds.width, referenceBounds.height))
    : 1000;
  const minorSpan = referenceBounds
    ? Math.max(Number.EPSILON * 100, Math.min(Math.abs(referenceBounds.width), Math.abs(referenceBounds.height)))
    : span;
  const positionTolerance = Math.max(
    Math.min(span * 0.0005, minorSpan * 0.001),
    Math.min((Number(mergeDistance) || 0) * 0.08, minorSpan * 0.001)
  );
  const angleTolerance = Math.max(0.04 * DEG, Math.min(0.18 * DEG, Math.atan2(positionTolerance * 0.08, span)));
  const sorted = (items || []).slice().sort((a,b) => {
    const rank = item => (item.line.importance || 0) + Math.min(20, (item.line.support || 0) * 2);
    return rank(b) - rank(a);
  });
  const merged = [];

  function measure(ext, angle) {
    const a=ext.p1,b=ext.p2;
    const ux=Math.cos(angle),uy=Math.sin(angle);
    const nx=-uy,ny=ux;
    const mid={x:(a.x+b.x)*0.5,y:(a.y+b.y)*0.5};
    const t1=a.x*ux+a.y*uy,t2=b.x*ux+b.y*uy;
    return {
      angle,
      offset:mid.x*nx+mid.y*ny,
      minT:Math.min(t1,t2),
      maxT:Math.max(t1,t2)
    };
  }

  function pointAt(angle,offset,t) {
    const ux=Math.cos(angle),uy=Math.sin(angle);
    const nx=-uy,ny=ux;
    return {x:ux*t+nx*offset,y:uy*t+ny*offset};
  }

  function intervalGap(a,b) {
    return Math.max(0,Math.max(a.minT,b.minT)-Math.min(a.maxT,b.maxT));
  }

  function rank(line) {
    return (line.importance||0)+Math.min(20,(line.support||0)*2);
  }

  for(const item of sorted) {
    if(!item||!item.line||!item.ext||!item.ext.p1||!item.ext.p2)continue;

    const angle=canonicalLineAngle(Math.atan2(
      item.ext.p2.y-item.ext.p1.y,
      item.ext.p2.x-item.ext.p1.x
    ));
    let state=measure(item.ext,angle);
    let stateWeight=Math.max(1,rank(item.line));
    const matched=new Set();
    let changed=true;

    // Expand the merged interval until no previously emitted interval touches
    // it. This makes consolidation transitive: A overlaps B, B overlaps C.
    while(changed) {
      changed=false;
      for(const existing of merged) {
        if(matched.has(existing))continue;
        if(lineAngleDiff(existing.measure.angle,angle)>angleTolerance)continue;
        const candidateMeasure=measure(existing.ext,angle);
        if(Math.abs(candidateMeasure.offset-state.offset)>positionTolerance)continue;
        if(intervalGap(candidateMeasure,state)>positionTolerance)continue;

        matched.add(existing);
        const weight=Math.max(1,rank(existing.line));
        state.offset=(state.offset*stateWeight+candidateMeasure.offset*weight)/(stateWeight+weight);
        stateWeight+=weight;
        state.minT=Math.min(state.minT,candidateMeasure.minT);
        state.maxT=Math.max(state.maxT,candidateMeasure.maxT);
        changed=true;
      }
    }

    if(!matched.size) {
      merged.push({line:item.line,ext:item.ext,measure:state});
      continue;
    }

    let winner=item.line;
    let maxRank=rank(winner);
    let maxImportance=winner.importance||0;
    let maxSupport=winner.support||0;
    for(const existing of matched) {
      const value=rank(existing.line);
      if(value>maxRank){winner=existing.line;maxRank=value;}
      maxImportance=Math.max(maxImportance,existing.line.importance||0);
      maxSupport=Math.max(maxSupport,existing.line.support||0);
    }
    const mergedLine=Object.assign({},winner,{
      angle,
      offset:0,
      importance:maxImportance,
      support:maxSupport,
      scopeKey:"merged"
    });
    const ext={
      p1:pointAt(angle,state.offset,state.minT),
      p2:pointAt(angle,state.offset,state.maxT)
    };

    for(let i=merged.length-1;i>=0;i--)if(matched.has(merged[i]))merged.splice(i,1);
    merged.push({line:mergedLine,ext,measure:measure(ext,angle)});
  }

  return merged.map(item=>({line:item.line,ext:item.ext}));
}

function positionlessTolerance(value) {
  return Math.max(Number.EPSILON * 100, Number(value) || 0);
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

function addAlignmentLineCandidates(points, origin, angle, tolerance, output, baseImportance, source, minimumAnchorSupport) {
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
    records.push({
      value:(p.x-origin.x)*nx+(p.y-origin.y)*ny,
      along:(p.x-origin.x)*ux+(p.y-origin.y)*uy,
      x:p.x,y:p.y,
      importance:p.importance||p.priority||0,
      isAnchor:p.alignmentKind !== "landmark"
    });
  }
  if(records.length<2)return;
  records.sort((x,y)=>x.value-y.value);
  const diagonal=Math.max(1,Math.hypot(maxX-minX,maxY-minY));
  const minAlongSpan=Math.max(tolerance*3.0,diagonal*0.045);
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
    let minAlong=Infinity,maxAlong=-Infinity,anchorSupport=0;
    for(const record of cluster.records){
      minAlong=Math.min(minAlong,record.along);
      maxAlong=Math.max(maxAlong,record.along);
      if(record.isAnchor)anchorSupport++;
    }
    const alongSpan=maxAlong-minAlong;
    // Two points always define a line mathematically, but not necessarily a
    // meaningful construction axis. Require three active anchors for inferred
    // alignments; direct structural edges are handled by their own segment path.
    if(anchorSupport<(Number.isInteger(minimumAnchorSupport)?minimumAnchorSupport:3) || alongSpan<minAlongSpan)continue;
    const support=cluster.records.length;
    rankedClusters.push({
      cluster,support,
      score:baseImportance+Math.min(18,cluster.maxImportance*0.12)+
        Math.min(14,anchorSupport*1.8)+Math.min(8,(alongSpan/diagonal)*20)
    });
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

function addFallbackCurveGuideCandidates(polyCurve, handles, output, bounds, maxGuides) {
  if (!Array.isArray(output)) return 0;
  const limit = Math.max(1, Math.min(6, Number.isInteger(maxGuides) ? maxGuides : 4));
  const diagonal = bounds
    ? Math.max(Number.EPSILON * 100, Math.hypot(bounds.width, bounds.height))
    : 1000;
  const positionTolerance = Math.max(Number.EPSILON * 100, diagonal * 0.0005);
  const selected = [];

  function append(candidate) {
    if (!candidate || !candidate.p1 || !Number.isFinite(candidate.p1.x) ||
        !Number.isFinite(candidate.p1.y) || !Number.isFinite(candidate.angle)) return;
    const angle = canonicalLineAngle(candidate.angle);
    const normalX = -Math.sin(angle), normalY = Math.cos(angle);
    const offset = candidate.p1.x * normalX + candidate.p1.y * normalY;
    const duplicate = selected.some(existing => {
      if (lineAngleDiff(existing.angle, angle) > 0.75 * DEG) return false;
      const existingOffset = existing.p1.x * (-Math.sin(existing.angle)) +
        existing.p1.y * Math.cos(existing.angle);
      return Math.abs(existingOffset - offset) <= positionTolerance;
    });
    if (!duplicate) selected.push(Object.assign({}, candidate, { angle }));
  }

  const extrema = [];
  addCurveExtremumTangents(polyCurve, extrema);
  extrema.sort((a, b) => (b.importance || 0) - (a.importance || 0));
  for (const candidate of extrema) {
    if (selected.length >= limit) break;
    append(candidate);
  }

  if (selected.length < limit) {
    const orderedHandles = (handles || []).filter(handle =>
      handle && handle.anchor && handle.handle &&
      Number.isFinite(handle.anchor.x) && Number.isFinite(handle.anchor.y) &&
      Number.isFinite(handle.handle.x) && Number.isFinite(handle.handle.y) &&
      dist(handle.anchor, handle.handle) > Number.EPSILON * 100
    ).slice().sort((a, b) => (b.baseLength || dist(b.anchor, b.handle)) -
      (a.baseLength || dist(a.anchor, a.handle)));

    for (const handle of orderedHandles) {
      if (selected.length >= limit) break;
      const dx = handle.handle.x - handle.anchor.x;
      const dy = handle.handle.y - handle.anchor.y;
      append({
        p1: { x: handle.anchor.x, y: handle.anchor.y },
        angle: Math.atan2(dy, dx),
        importance: 66,
        support: 1,
        source: "fallback-bezier-tangent",
        componentId: Number.isInteger(handle.componentId) ? handle.componentId : undefined,
        scopeKey: Number.isInteger(handle.componentId) ? "component:" + handle.componentId : undefined
      });
    }
  }

  output.push.apply(output, selected);
  return selected.length;
}

function addBezierTangentCandidates(polyCurve, handles, output, includeRawCurves) {
  for (const h of (handles || [])) {
    if (!h || !h.anchor || !h.handle) continue;
    const dx = h.handle.x - h.anchor.x;
    const dy = h.handle.y - h.anchor.y;
    if (Math.hypot(dx, dy) <= Number.EPSILON * 100) continue;
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
        if (Math.hypot(v.dx, v.dy) <= Number.EPSILON * 100) continue;
        output.push({ p1: v.p, angle: Math.atan2(v.dy, v.dx), importance: 58, support: 1, source: "bezier-tangent" });
      }
      const localCurveScale = Math.max(
        dist(b.start, b.c1), dist(b.c1, b.c2), dist(b.c2, b.end), Number.EPSILON * 100
      );
      for (const t of cubicInflectionParametersAccurate(b)) {
        const mt = 1 - t;
        const dx = 3 * mt * mt * (b.c1.x - b.start.x) + 6 * mt * t * (b.c2.x - b.c1.x) + 3 * t * t * (b.end.x - b.c2.x);
        const dy = 3 * mt * mt * (b.c1.y - b.start.y) + 6 * mt * t * (b.c2.y - b.c1.y) + 3 * t * t * (b.end.y - b.c2.y);
        if (Math.hypot(dx, dy) <= localCurveScale * 1e-9) continue;
        output.push({ p1: cubicPoint(b, t), angle: Math.atan2(dy, dx), importance: 42, support: 1, source: "bezier-inflection" });
      }
    }
  }
}

// Seleção visual dos handles: conserva as coordenadas Bézier reais, reduz
// marcadores quando existe espaço e omite os que inevitavelmente colidiriam.
// Isto afeta apenas a apresentação, nunca a geometria da curva original.
function projectHandlePositions(handles, multiplier) {
  const factor = Math.max(1, Number(multiplier) || 1);
  return (handles || []).map(h => {
    const dx = h.handle.x - h.anchor.x;
    const dy = h.handle.y - h.anchor.y;
    const actualLength = Math.hypot(dx, dy);
    if (actualLength <= EPS || factor <= 1 + 1e-9) {
      return Object.assign({}, h, { stemProjected: false });
    }
    const ux = dx / actualLength, uy = dy / actualLength;
    const projectedLength = actualLength * factor;
    return Object.assign({}, h, {
      handle: { x: h.anchor.x + ux * projectedLength, y: h.anchor.y + uy * projectedLength },
      stemProjected: true
    });
  });
}

function buildCollisionSafeHandles(handles, anchors, baseHandleSize, allowScaling) {
  if (!handles || handles.length === 0) return [];

  const baseRadius = Math.max(Number.EPSILON * 100, baseHandleSize / 2);
  const minRadius = baseRadius * 0.22;
  const clearanceGap = baseRadius * 0.18;

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
  let totalWeight = 0, straightWeight = 0, curveWeight = 0, primitiveId = 0;
  const bounds = geom && geom.bounds ? geom.bounds : { width: 100, height: 100 };
  const diagonal = Math.max(Number.EPSILON * 100, Math.hypot(bounds.width, bounds.height));
  const components = (geom && geom.componentModel && geom.componentModel.components) || [];
  const componentById = new Map(components.map(component => [component.id, component]));
  const curveToComponent = new Map();
  for (const component of components) {
    for (let index = component.curveStart; index < component.curveStart + component.curveCount; index++) {
      curveToComponent.set(index, component.id);
    }
  }

  function componentScale(component) {
    const bounds = component && component.bounds;
    if (!bounds || !Number.isFinite(bounds.width) || !Number.isFinite(bounds.height)) return diagonal;
    return Math.max(Number.EPSILON * 100, Math.hypot(bounds.width, bounds.height));
  }

  function componentForCurve(curveIndex) {
    return curveToComponent.has(curveIndex) ? curveToComponent.get(curveIndex) : -1;
  }

  for (const seg of (geom.straightSegments || [])) {
    if (!seg || !seg.p1 || !seg.p2) continue;
    const length = dist(seg.p1, seg.p2);
    const component = componentById.get(seg.componentId);
    const componentDiagonal = componentScale(component);
    if (length < (component ? componentDiagonal : diagonal) * 0.002) continue;
    const angle = canonicalLineAngle(Math.atan2(seg.p2.y - seg.p1.y, seg.p2.x - seg.p1.x));
    const weight = Math.min(length, (component ? componentDiagonal : diagonal) * 0.75);
    evidence.push({
      angle, weight, source: "edge", primitive: "edge-" + primitiveId++,
      componentId: Number.isInteger(seg.componentId) ? seg.componentId : -1
    });
    straightWeight += weight;
    totalWeight += weight;
  }

  if (polyCurve && polyCurve.curveCount) {
    for (let c = 0; c < polyCurve.curveCount; c++) {
      const curve = polyCurve.at(c);
      const beziers = collectBeziers(curve);
      const componentId = componentForCurve(c);
      const component = componentById.get(componentId);
      const componentDiagonal = componentScale(component);
      const minUsefulLength = (component ? componentDiagonal : diagonal) * 0.002;
      for (let bIdx = 0; bIdx < beziers.length; bIdx++) {
        const b = beziers[bIdx];
        const primitive = "curve-" + c + "-" + bIdx;
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
          evidence.push({ angle, weight, source: "curve", primitive, componentId });
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
  if (!samples.length) return [];

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
  const diagonal = Math.max(Number.EPSILON * 100, Math.hypot(bounds.width, bounds.height));
  const minorDimension = Math.max(diagonal * 0.04, Math.min(Math.abs(bounds.width), Math.abs(bounds.height)));
  // A wordmark's width must not erase the small but real spacing unit between
  // glyphs. Use the minor mark dimension as the second scale reference.
  const tolerance = Math.max(diagonal * 0.0003, minorDimension * 0.0022);
  const positions = mergeProjectedPositions(points, angle, tolerance);
  if (positions.length < 5) return null;

  const gaps = [];
  for (let i = 1; i < positions.length; i++) {
    const gap = positions[i].mean - positions[i - 1].mean;
    if (gap >= Math.max(diagonal * 0.0018, minorDimension * 0.008) && gap <= diagonal * 0.55) gaps.push(gap);
  }
  if (gaps.length < 3) return null;

  const minUnit = Math.max(diagonal * 0.0018, minorDimension * 0.009);
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
  const bounds=geom.bounds;
  const diagonal=Math.max(Number.EPSILON*100,Math.hypot(bounds.width,bounds.height));
  const dedupeTolerance=diagonal*1e-5;
  const raw=[];
  for(const a of (geom.anchors||[]))if(a&&Number.isFinite(a.x)&&Number.isFinite(a.y))
    raw.push({x:a.x,y:a.y,importance:Number(a.importance||a.priority||30)});
  for(const l of (geom.landmarks||[]))if(l&&Number.isFinite(l.x)&&Number.isFinite(l.y))
    raw.push({x:l.x,y:l.y,importance:Number(l.importance||45)});
  raw.sort((a,b)=>b.importance-a.importance);
  const points=[],buckets=new Map(),cell=Math.max(dedupeTolerance,Number.EPSILON*100);
  const key=(x,y)=>x+","+y;
  for(const p of raw){
    const gx=Math.floor(p.x/cell),gy=Math.floor(p.y/cell);let duplicate=false;
    for(let dx=-1;dx<=1&&!duplicate;dx++)for(let dy=-1;dy<=1&&!duplicate;dy++){
      const bucket=buckets.get(key(gx+dx,gy+dy));
      if(bucket&&bucket.some(q=>dist(q,p)<=dedupeTolerance))duplicate=true;
    }
    if(duplicate)continue;
    const item={x:p.x,y:p.y,importance:p.importance};points.push(item);
    const k=key(gx,gy);if(!buckets.has(k))buckets.set(k,[]);buckets.get(k).push(item);
  }
  const maxPoints=220;let analysisPoints=points;
  if(points.length>maxPoints){
    // Farthest-point sampling preserves coverage across separate glyphs and contours.
    const selected=[points[0]],chosen=new Set([0]);
    const nearest=points.map((p,i)=>i===0?0:dist(p,selected[0]));
    while(selected.length<maxPoints){
      let bestIndex=-1,bestScore=-Infinity;
      for(let i=0;i<points.length;i++){
        if(chosen.has(i))continue;
        const score=nearest[i]*(1+clamp(points[i].importance,0,100)/100*0.12);
        if(score>bestScore){bestScore=score;bestIndex=i;}
      }
      if(bestIndex<0)break;chosen.add(bestIndex);selected.push(points[bestIndex]);
      const picked=points[bestIndex];
      for(let i=0;i<points.length;i++)if(!chosen.has(i)){
        const d=dist(points[i],picked);if(d<nearest[i])nearest[i]=d;
      }
    }
    analysisPoints=selected;
  }
  if(analysisPoints.length<4)return{module:0,phase:0,angle:0,ratios:[],confidence:0,axes:[]};
  const axesToTest=[];
  function addAxis(angle,weight,source){
    const a=canonicalLineAngle(angle);
    if(axesToTest.some(x=>lineAngleDiff(x.angle,a)<2*DEG))return;
    axesToTest.push({angle:a,weight:weight||0,source:source||"direction-family"});
  }
  for(const family of(directionFamilies||[]).slice(0,4)){
    addAxis(family.angle,family.weight,"family");addAxis(family.angle+Math.PI/2,family.weight*0.88,"perpendicular");
  }
  if(!axesToTest.length){
    const fallback=geom.dominantAngle||0;addAxis(fallback,0,"fallback");addAxis(fallback+Math.PI/2,0,"fallback-perpendicular");
  }
  const results=[];
  for(const axis of axesToTest.slice(0,8)){
    const result=evaluateProjectedModule(analysisPoints,bounds,axis.angle,axis.weight);
    if(!result)continue;result.source=axis.source;results.push(result);
  }
  results.sort((a,b)=>b.score-a.score);const selected=[];
  for(const candidate of results){
    const duplicate=selected.some(existing=>
      lineAngleDiff(existing.angle,candidate.angle)<2*DEG&&
      Math.abs(existing.module-candidate.module)<=Math.max(diagonal*0.0012,candidate.module*0.035)
    );
    if(duplicate)continue;selected.push(candidate);if(selected.length>=4)break;
  }
  const primary=selected[0]||null;
  return{
    module:primary?primary.module:0,phase:primary?primary.phase:0,angle:primary?primary.angle:0,
    ratios:primary?primary.ratios:[],confidence:primary?primary.confidence:0,
    axes:selected,pointCount:analysisPoints.length,sourcePointCount:points.length
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
  const diagonal = Math.max(Number.EPSILON * 100, Math.hypot(bounds.width, bounds.height));
  const minorDimension = Math.max(
    Number.EPSILON * 100,
    Math.min(Math.abs(bounds.width), Math.abs(bounds.height))
  );
  const minRadius = Math.max(diagonal * 1e-6, minorDimension * 0.0025);
  const maxRadius = diagonal * 2.25;

  // Keep separate close rings distinct. The actual short side controls the
  // tolerance, while a tiny diagonal-relative floor absorbs numeric noise.
  const centreTolerance = Math.max(diagonal * 1e-5, minorDimension * 0.0025);
  const radiusTolerance = circle => Math.max(minorDimension * 0.0005, circle.r * 0.012);
  const unique = [];

  function addSupport(target, input) {
    const sourceKey = [
      Number.isInteger(input.componentId) ? input.componentId : -1,
      Number.isInteger(input.contourIndex) ? input.contourIndex : -1,
      Number.isInteger(input.segmentIndex) ? input.segmentIndex : -1
    ].join(":");
    if (target.sourceKeys.has(sourceKey)) return;
    target.sourceKeys.add(sourceKey);

    const componentId = Number.isInteger(input.componentId) ? input.componentId : -1;
    const contourIndex = Number.isInteger(input.contourIndex) ? input.contourIndex : -1;
    let contour = target.contourSupports.find(item =>
      item.componentId === componentId && item.contourIndex === contourIndex
    );
    if (!contour) {
      contour = {
        componentId,
        contourIndex,
        segments: [],
        totalSegments: Math.max(1, input.contourSegmentCount || 1)
      };
      target.contourSupports.push(contour);
    }
    contour.totalSegments = Math.max(contour.totalSegments, input.contourSegmentCount || 1);
    const segmentIndex = Number.isInteger(input.segmentIndex) ? input.segmentIndex : -1;
    if (!contour.segments.includes(segmentIndex)) contour.segments.push(segmentIndex);
  }

  for (let inputIndex = 0; inputIndex < (rawCircles || []).length; inputIndex++) {
    const input = rawCircles[inputIndex];
    if (!input || !Number.isFinite(input.cx) || !Number.isFinite(input.cy) || !Number.isFinite(input.r)) continue;
    if (input.r < minRadius || input.r > maxRadius) continue;

    const confidence = Number.isFinite(input.confidence) ? clamp(input.confidence, 0, 1) : 0;
    if (confidence < 0.16) continue;

    const margin = diagonal * 1.25;
    if (input.cx < bounds.x - margin || input.cx > bounds.x + bounds.width + margin ||
        input.cy < bounds.y - margin || input.cy > bounds.y + bounds.height + margin) continue;

    const componentId = Number.isInteger(input.componentId) ? input.componentId : -1;
    const contourIndex = Number.isInteger(input.contourIndex) ? input.contourIndex : -1;
    const scopeKey = input.circleScopeKey ||
      ("component:" + componentId);
    const segmentIndex = Number.isInteger(input.segmentIndex) ? input.segmentIndex : inputIndex;

    const existing = unique.find(circle =>
      circle.scopeKey === scopeKey &&
      circle.componentId === componentId &&
      circle.contourIndex === contourIndex &&
      Math.hypot(circle.cx - input.cx, circle.cy - input.cy) <= centreTolerance &&
      Math.abs(circle.r - input.r) <= radiusTolerance(input)
    );

    if (existing) {
      if (!existing.segmentIndexes.includes(segmentIndex)) {
        const weight = Math.max(0.05, confidence);
        const total = existing.weight + weight;
        existing.cx = (existing.cx * existing.weight + input.cx * weight) / total;
        existing.cy = (existing.cy * existing.weight + input.cy * weight) / total;
        existing.r = (existing.r * existing.weight + input.r * weight) / total;
        existing.weight = total;
        existing.segmentIndexes.push(segmentIndex);
        addSupport(existing, input);
      }
      existing.confidence = Math.max(existing.confidence, confidence);
    } else {
      const circle = {
        cx: input.cx,
        cy: input.cy,
        r: input.r,
        confidence,
        weight: Math.max(0.05, confidence),
        componentId,
        contourIndex,
        scopeKey,
        segmentIndexes: [segmentIndex],
        sourceKeys: new Set(),
        contourSupports: []
      };
      addSupport(circle, input);
      unique.push(circle);
    }
  }

  // Cluster only within one selected group/component and only when every
  // centre remains mutually close. This avoids transitive centre drift.
  const families = [];
  for (const circle of unique) {
    let selected = null;
    let bestDistance = Infinity;
    for (const family of families) {
      if (family.scopeKey !== circle.scopeKey) continue;
      const distance = Math.hypot(family.cx - circle.cx, family.cy - circle.cy);
      if (distance > centreTolerance) continue;
      if (!family.centres.every(point =>
        Math.hypot(point.x - circle.cx, point.y - circle.cy) <= centreTolerance
      )) continue;
      if (distance < bestDistance) {
        selected = family;
        bestDistance = distance;
      }
    }

    if (!selected) {
      selected = {
        cx: circle.cx,
        cy: circle.cy,
        scopeKey: circle.scopeKey,
        componentId: circle.componentId,
        mixedComponents: false,
        circles: [],
        centres: [],
        confidence: 0,
        centreSpread: 0
      };
      families.push(selected);
    }

    if (selected.componentId !== circle.componentId) {
      selected.componentId = undefined;
      selected.mixedComponents = true;
    }
    selected.centres.push({ x: circle.cx, y: circle.cy });
    selected.circles.push(circle);
    const n = selected.centres.length;
    selected.cx += (circle.cx - selected.cx) / n;
    selected.cy += (circle.cy - selected.cy) / n;
  }

  const displayCircles = [];
  const confirmedFamilies = [];

  for (const family of families) {
    family.centreSpread = family.centres.length > 1
      ? Math.max(...family.centres.map(point => Math.hypot(point.x - family.cx, point.y - family.cy)))
      : 0;
    if (family.centreSpread > centreTolerance) continue;

    const radiusTiers = [];
    family.circles.sort((a,b) => a.r - b.r);

    for (const circle of family.circles) {
      let tier = radiusTiers.find(item => Math.abs(item.r - circle.r) <= radiusTolerance(circle));
      if (!tier) {
        tier = {
          r: circle.r,
          confidence: circle.confidence,
          weight: 0,
          sourceKeys: new Set(),
          contourSupports: []
        };
        radiusTiers.push(tier);
      }

      const weight = Math.max(1, circle.segmentIndexes.length);
      tier.r = (tier.r * tier.weight + circle.r * weight) / (tier.weight + weight);
      tier.weight += weight;
      tier.confidence = Math.max(tier.confidence, circle.confidence);

      for (const sourceKey of circle.sourceKeys) tier.sourceKeys.add(sourceKey);
      for (const support of circle.contourSupports) {
        let target = tier.contourSupports.find(item =>
          item.componentId === support.componentId && item.contourIndex === support.contourIndex
        );
        if (!target) {
          target = {
            componentId: support.componentId,
            contourIndex: support.contourIndex,
            segments: [],
            totalSegments: support.totalSegments || 1
          };
          tier.contourSupports.push(target);
        }
        target.totalSegments = Math.max(target.totalSegments, support.totalSegments || 1);
        for (const segment of support.segments) {
          if (!target.segments.includes(segment)) target.segments.push(segment);
        }
      }
    }

    // Balanced evidence rule:
    // - two distinct Bézier segments from one contour can establish a circle;
    // - otherwise two high-confidence fragments from sibling vectors in the
    //   same selected group can establish the shared circle.
    // A single rounded corner/curve is never enough on its own.
    const supportedTiers = radiusTiers.filter(tier => {
      const supportRecords = tier.contourSupports;
      const distinctSegments = tier.sourceKeys.size;
      const sameContourSupport = supportRecords.some(item =>
        item.segments.length >= 2 &&
        item.segments.length / Math.max(1, item.totalSegments || 1) >= 0.30
      );
      const independentVectorSupport = supportRecords.filter(item =>
        item.segments.length >= 1
      ).length;
      const averageConfidence = tier.confidence;
      const groupedSupport = independentVectorSupport >= 2 &&
        distinctSegments >= 2 &&
        averageConfidence >= 0.72;

      tier.segmentSupport = distinctSegments;
      tier.segmentCoverage = supportRecords.reduce((maximum,item) =>
        Math.max(maximum,item.segments.length / Math.max(1,item.totalSegments || 1)),0);
      tier.contourSupportCount = supportRecords.filter(item => item.segments.length >= 2).length;

      return sameContourSupport || groupedSupport;
    });
    if (!supportedTiers.length) continue;

    family.circles = supportedTiers.sort((a,b) => a.r - b.r).map(tier => ({
      r: tier.r,
      confidence: tier.confidence,
      samples: tier.segmentSupport,
      contourSupportCount: tier.contourSupportCount,
      segmentCoverage: tier.segmentCoverage
    }));

    family.confidence = family.circles.reduce((sum,circle) => sum + circle.confidence,0) /
      family.circles.length;
    family.confidence *= clamp(
      1 - family.centreSpread / Math.max(centreTolerance,EPS),
      0.35,1
    );

    const radii = family.circles.map(circle => circle.r);
    const gaps = [];
    for(let i=1;i<radii.length;i++) gaps.push(radii[i]-radii[i-1]);

    let radiusModule = 0;
    let radiusModuleConfidence = 0;
    if(gaps.length>=2) {
      const sortedGaps = gaps.slice().sort((a,b) => a-b);
      const median = sortedGaps[Math.floor(sortedGaps.length/2)];
      const close = gaps.filter(gap =>
        Math.abs(gap-median) <= Math.max(minorDimension*0.0006,median*0.045)
      );
      if(median>=minRadius && close.length>=2) {
        radiusModule = close.reduce((sum,gap) => sum+gap,0)/close.length;
        radiusModuleConfidence = close.length/gaps.length*family.confidence;
      }
    }
    family.radiusModule = radiusModule;
    family.radiusModuleConfidence = radiusModuleConfidence;
    family.radiusRatios = [];

    if(radii.length>=2) {
      const base = radii[0];
      for(let i=1;i<radii.length;i++) {
        const ratio = approximateSmallRatio(radii[i]/base,6);
        if(ratio) family.radiusRatios.push({
          innerRadius:base,
          outerRadius:radii[i],
          ratio,
          confidence:Math.min(family.confidence,1-ratio.error*8)
        });
      }
    }

    const rankedTiers = family.circles.slice().sort((a,b) =>
      (b.samples*2+b.confidence)-(a.samples*2+a.confidence)
    );
    for(const tier of rankedTiers.slice(0,3)) {
      displayCircles.push({
        cx:family.cx,
        cy:family.cy,
        r:tier.r,
        confidence:tier.confidence,
        support:tier.samples,
        contourSupportCount:tier.contourSupportCount,
        componentId:Number.isInteger(family.componentId) ? family.componentId : undefined,
        scopeKey:family.scopeKey,
        familySize:family.circles.length
      });
    }

    delete family.centres;
    delete family.mixedComponents;
    confirmedFamilies.push(family);
  }

  displayCircles.sort((a,b) =>
    (b.confidence+Math.min(0.2,b.support*0.025))-
    (a.confidence+Math.min(0.2,a.support*0.025))
  );

  return {
    circles:displayCircles.slice(0,48),
    families:confirmedFamilies,
    relationCount:confirmedFamilies.reduce((sum,family) => sum+family.radiusRatios.length,0)
  };
}

function classifyGeometryProfile(geom) {
  const totalSegments=Math.max(1,geom.totalSegmentCount||0);
  const straightRatio=clamp((geom.straightSegmentCount||0)/totalSegments,0,1);
  const curveRatio=clamp((geom.curveSegmentCount||0)/totalSegments,0,1);
  const contourTotal=Math.max(1,geom.contourCount||1);
  const openRatio=clamp((geom.openContourCount||0)/contourTotal,0,1);
  const width=Math.max(Number.EPSILON,geom.bounds.width||0);
  const height=Math.max(Number.EPSILON,geom.bounds.height||0);
  const aspect=Math.max(width,height)/Math.min(width,height);
  const symmetry=clamp((geom.symmetry&&geom.symmetry.score)||0,0,1);
  const moduleConfidence=clamp((geom.modules&&geom.modules.confidence)||0,0,1);
  const circleCount=(geom.circleFamilies||[]).filter(f=>f&&f.confidence>=0.55&&f.circles&&f.circles.length>=2).length;
  const circleSignal=clamp(circleCount/2,0,1);
  const multiContour=clamp(((geom.contourCount||0)-1)/4,0,1);
  const componentCount = Math.max(1, (geom.componentModel && geom.componentModel.componentCount) || 1);
  const componentSignal = clamp((componentCount - 1) / 5, 0, 1);
  const componentDirectionSignal = clamp(
    ((geom.componentAnalysis || []).filter(c => c.localStraightEdgeCount >= 2).length) / Math.max(1, componentCount),
    0, 1
  );
  const scores={
    geometric:clamp(0.24*straightRatio+0.24*symmetry+0.24*moduleConfidence+0.20*circleSignal+0.08*(1-openRatio),0,1),
    typographic:clamp(0.14*clamp((aspect-1.1)/2.4,0,1)+0.18*multiContour+0.18*componentSignal+0.16*componentDirectionSignal+0.14*straightRatio+0.10*curveRatio+0.10*(1-openRatio),0,1),
    handwriting:clamp(0.38*openRatio+0.30*curveRatio+0.18*(1-symmetry)+0.14*(1-straightRatio),0,1),
    organic:clamp(0.48*curveRatio+0.24*(1-symmetry)+0.16*(1-moduleConfidence)+0.12*(1-circleSignal),0,1),
    radial:geom.isRadialArray?1:0
  };
  const ranked=Object.keys(scores).sort((a,b)=>scores[b]-scores[a]);
  return {suggested:ranked[0],confidence:scores[ranked[0]],scores,metrics:{straightRatio,curveRatio,openRatio,aspect,symmetry,moduleConfidence,circleSignal,multiContour,componentCount,componentSignal,componentDirectionSignal}};
}

function enrichGeometryAnalysis(polyCurve, geom) {
  const evidence = collectDirectionEvidence(polyCurve, geom);
  const families = detectDirectionFamilies(evidence, geom.dominantAngle);
  const primaryAngle = families.length ? families[0].angle : geom.dominantAngle;
  const moduleSystems = detectModularSystems(geom, families);
  const circleAnalysis = refineCircleCandidates(geom.rawCircleCandidates || geom.circles, geom.bounds);

  // Derived analysis is attached alongside, never written into the anchors,
  // handles, Bézier records, radial petals or original circle candidates.
  geom.directionEvidence = evidence;
  geom.directionFamilies = families;
  geom.modules = moduleSystems;
  geom.circleFamilies = circleAnalysis.families;
  // Render representative circles supported by clustered Bézier fits. The
  // complete geometry candidates remain available for analysis and metrics.
  geom.refinedCircles = circleAnalysis.circles;
  const hasBezierCircleEvidence = (geom.rawCircleCandidates || []).length > 0;
  const validatedRadialCircles = !hasBezierCircleEvidence && geom.isRadialArray
    ? (geom.circles || []).filter(circle =>
        circle && Number.isFinite(circle.cx) && Number.isFinite(circle.cy) &&
        Number.isFinite(circle.r) && circle.r > 0 && !Number.isFinite(circle.confidence))
    : [];
  geom.displayCircles = circleAnalysis.circles.length > 0
    ? circleAnalysis.circles
    : validatedRadialCircles;
  geom.circleRelationCount = circleAnalysis.relationCount;
  if (lineAngleDiff(primaryAngle, geom.dominantAngle) > 0.75 * DEG) {
    geom.symmetry = detectAxisSymmetry(geom.anchors, primaryAngle);
  }
  const componentFeatures = new Map();
  function addComponentFeature(componentId, key, value) {
    if (!Number.isInteger(componentId) || componentId < 0) return;
    if (!componentFeatures.has(componentId)) componentFeatures.set(componentId, {
      anchors: [], landmarks: [], edges: [], samples: [], circles: []
    });
    componentFeatures.get(componentId)[key].push(value);
  }
  for (const anchor of (geom.anchors || [])) {
    for (const id of (anchor.componentIds || [])) addComponentFeature(id, "anchors", anchor);
  }
  for (const value of (geom.landmarks || [])) addComponentFeature(value.componentId, "landmarks", value);
  for (const value of (geom.straightSegments || [])) addComponentFeature(value.componentId, "edges", value);
  for (const value of (evidence.samples || [])) addComponentFeature(value.componentId, "samples", value);
  for (const value of (geom.rawCircleCandidates || [])) addComponentFeature(value.componentId, "circles", value);

  geom.componentAnalysis = (geom.componentMetrics || []).map(component => {
    const localData = componentFeatures.get(component.id) || {
      anchors: [], landmarks: [], edges: [], samples: [], circles: []
    };
    const localAnchors = localData.anchors;
    const localLandmarks = localData.landmarks;
    const localEdges = localData.edges;
    const localAngle = localEdges.length ? detectDominantDirection(localEdges) : geom.dominantAngle;
    const localBounds = component.bounds &&
      Number.isFinite(component.bounds.x) && Number.isFinite(component.bounds.y) &&
      component.bounds.width > 0 && component.bounds.height > 0
      ? component.bounds : geom.bounds;
    const localSamples = localData.samples;
    const localEvidence = {
      samples: localSamples,
      totalWeight: localSamples.reduce((sum, sample) => sum + sample.weight, 0),
      straightWeight: localSamples.filter(sample => sample.source === "edge").reduce((sum, sample) => sum + sample.weight, 0),
      curveWeight: localSamples.filter(sample => sample.source === "curve").reduce((sum, sample) => sum + sample.weight, 0),
      diagonal: Math.max(Number.EPSILON * 100, Math.hypot(localBounds.width, localBounds.height))
    };
    const localFamilies = localSamples.length
      ? detectDirectionFamilies(localEvidence, localAngle)
      : [];
    const localGeometry = {
      bounds: localBounds,
      anchors: localAnchors,
      landmarks: localLandmarks,
      dominantAngle: localAngle
    };
    const hasLocalAxisEvidence = localFamilies.length > 0 || localEdges.length >= 3;
    const localModules = hasLocalAxisEvidence
      ? detectModularSystems(localGeometry, localFamilies)
      : { module: 0, phase: 0, angle: 0, ratios: [], confidence: 0, axes: [] };
    const localCircleInputs = localData.circles;
    const localCircleAnalysis = refineCircleCandidates(localCircleInputs, localBounds);
    const localSymmetry = localAnchors.length >= 3
      ? detectAxisSymmetry(localAnchors, localAngle)
      : { score: 0, axis: localAngle, longitudinal: 0, transverse: 0 };
    const localProportionRelations = [];
    for (const axis of localModules.axes || []) {
      for (const ratio of axis.ratios || []) {
        if (ratio > 1) localProportionRelations.push({
          type: "linear-module", ratio, angle: axis.angle, confidence: axis.confidence
        });
      }
    }
    for (const family of localCircleAnalysis.families || []) {
      for (const relation of family.radiusRatios || []) {
        localProportionRelations.push({
          type: "circle-radius",
          centre: { x: family.cx, y: family.cy },
          relation,
          confidence: relation.confidence
        });
      }
    }
    return Object.assign({}, component, {
      localDominantAngle: localAngle,
      localDirectionFamilies: localFamilies,
      localSymmetry,
      localStraightEdgeCount: localEdges.length,
      localAnchorCount: localAnchors.length,
      localLandmarkCount: localLandmarks.length,
      localModules,
      localCircleFamilies: localCircleAnalysis.families,
      localCircleRelationCount: localCircleAnalysis.relationCount,
      localProportionRelations
    });
  });  geom.profile = classifyGeometryProfile(geom);
  geom.proportionRelations = [];
  for (const component of (geom.componentAnalysis || [])) {
    for (const relation of (component.localProportionRelations || [])) {
      geom.proportionRelations.push(Object.assign({
        scope: "component",
        componentId: component.id,
        componentLabel: component.label
      }, relation));
    }
  }
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

function createModuleGridCandidates(axis, bounds, origin, output, mergeTolerance, options) {
  if (!axis || !Number.isFinite(axis.module) || axis.module <= 0 || axis.confidence < 0.70) return;
  const settings = options || {};
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

  const centreK = Math.round((originP - axis.phase) / axis.module);
  const maxLines = Math.max(1, Math.min(5, settings.maxLines || 5));
  const selectedK = [centreK];
  for (let i = 1; selectedK.length < maxLines; i++) selectedK.push(centreK - i, centreK + i);
  const validK = selectedK.filter((k,index,array) =>
    k >= firstK && k <= lastK && array.indexOf(k) === index
  ).slice(0,maxLines);

  let ordinal = 0;
  for (const k of validK) {
    const projection = axis.phase + k * axis.module;
    const offset = projection - originP;
    const major = ordinal % 2 === 0;
    output.push({
      p1: origin,
      angle: axis.angle,
      offset,
      importance: settings.importance || (major ? 70 : 57),
      support: axis.support || 0,
      source: settings.source || "modular-grid",
      moduleMajor: major,
      moduleIndex: k,
      moduleValue: axis.module,
      componentId: Number.isInteger(settings.componentId) ? settings.componentId : undefined,
      scopeKey: settings.scopeKey || undefined,
      clipBounds: settings.clipBounds || undefined
    });
    ordinal++;
  }
}

function addCircleFamilyConstructionCandidates(circleFamilies, output, options) {
  const settings = options || {};
  for (const family of (circleFamilies || []).slice(0, settings.maxFamilies || 4)) {
    if (!family || family.circles.length < 2 || family.confidence < (settings.minConfidence || 0.42)) continue;
    const circles = family.circles.slice().sort((a,b) => a.r-b.r);
    const hasMeasuredRelation = family.radiusRatios.length > 0 || family.radiusModuleConfidence >= 0.60;
    if (!hasMeasuredRelation) continue;

    const outerCircle = circles[circles.length - 1];
    const extentRadius = outerCircle.r;
    if (!Number.isFinite(extentRadius) || extentRadius <= 0) continue;

    // Each centre family gets its own local clipping rectangle and identity.
    // This matters when one Curve layer contains several glyphs/circular details.
    const clipBounds = settings.clipBounds || {
      x: family.cx - extentRadius,
      y: family.cy - extentRadius,
      width: extentRadius * 2,
      height: extentRadius * 2
    };
    const componentId = Number.isInteger(settings.componentId)
      ? settings.componentId
      : (Number.isInteger(family.componentId) ? family.componentId : undefined);
    const scopeKey = settings.scopeKey ||
      ("circle-family:" + (Number.isInteger(componentId) ? componentId : "global") +
       ":" + family.cx.toFixed(3) + ":" + family.cy.toFixed(3));
    const metadata = {
      componentId,
      scopeKey,
      clipBounds
    };

    const axisImportance = settings.importance || 64;
    const axisSource = settings.axisSource || "circle-centre-axis";
    const boundarySource = settings.boundarySource || "circle-ratio-boundary";
    output.push(Object.assign({
      p1:{x:family.cx,y:family.cy},angle:0,
      importance:axisImportance,source:axisSource
    },metadata));
    output.push(Object.assign({
      p1:{x:family.cx,y:family.cy},angle:Math.PI/2,
      importance:axisImportance,source:axisSource
    },metadata));

    // One pair of outer tangency limits is enough to communicate the family's
    // overall construction diameter; drawing four lines for every radius tier
    // created unnecessary nested rectangles around each glyph.
    const radius = outerCircle.r;
    const importance = settings.importance || (48 + outerCircle.confidence * 8);
    output.push(Object.assign({
      p1:{x:family.cx+radius,y:family.cy},angle:Math.PI/2,
      importance,source:boundarySource
    },metadata));
    output.push(Object.assign({
      p1:{x:family.cx-radius,y:family.cy},angle:Math.PI/2,
      importance,source:boundarySource
    },metadata));
    output.push(Object.assign({
      p1:{x:family.cx,y:family.cy+radius},angle:0,
      importance,source:boundarySource
    },metadata));
    output.push(Object.assign({
      p1:{x:family.cx,y:family.cy-radius},angle:0,
      importance,source:boundarySource
    },metadata));
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
  };
}

function appendStyledGridLine(defs, line, ext, styles, noFill) {
  if (!ext || dist(ext.p1, ext.p2) <= Number.EPSILON * 100) return;
  function add(a, b, style) {
    if (dist(a, b) <= Number.EPSILON * 100) return;
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

  if (isPrimary) add(ext.p1, ext.p2, styles.primary);
  else if (isSecondary) add(ext.p1, ext.p2, styles.secondary);
  else add(ext.p1, ext.p2, styles.auxiliary || styles.secondary);
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
  const extractedGeometry = extractCompositePolyCurve(rawSel);
  const polyCurve = extractedGeometry ? extractedGeometry.polyCurve : null;
  const componentModel = extractedGeometry ? {
    components: extractedGeometry.components,
    groups: extractedGeometry.groups,
    componentCount: extractedGeometry.componentCount,
    groupCount: extractedGeometry.groupCount,
    totalCurveCount: extractedGeometry.totalCurveCount,
    maxDepth: extractedGeometry.maxDepth
  } : null;
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

  const initialBaseGeometry = analyzeSmartGeometry(polyCurve, 9, 9, componentModel);
  initialBaseGeometry.componentModel = componentModel;
  const initialGeom = enrichGeometryAnalysis(polyCurve, initialBaseGeometry);
  const initialExactBounds = getExactCurveBounds(polyCurve) || initialGeom.bounds;
  const initialScaleContext = createGeometryScaleContext(initialExactBounds);
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
  const initialHasCircles = (initialGeom.displayCircles || []).length > 0;
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
  attachTip(showAnchorsSwitch, "Controla apenas a apresentação visual dos nós. A análise das Construction Gridlines continua a usar a geometria original, mesmo quando os marcadores Anchor Nodes estão ocultos.");

  const gridGrp = colLeft.addGroup("2. Smart Geometry & Grid");
  const analysisProfileCombo = gridGrp.addComboBox("Analysis Profile", [
    "Automatic (" + initialGeom.profile.suggested + ")",
    "Geometric Symbol",
    "Typographic / Letterform",
    "Handwriting / Lettering",
    "Organic / Freeform",
    "Radial / Repeating"
  ], 0);
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

  attachTip(analysisProfileCombo, "Perfil sugerido por métricas geométricas: " + initialGeom.profile.suggested + ". Componentes vectoriais: " + ((componentModel && componentModel.componentCount) || 1) + "; grupos: " + ((componentModel && componentModel.groupCount) || 0) + ". A escolha automática é heurística, não reconhecimento semântico de letras.");
  attachTip(gridModeCombo, "Smart Adaptive combina alinhamentos estruturais, módulos e, quando faltam eixos suficientes, tangentes Bézier exactas nos extremos e pontos de controlo. Evita impor uma única orientação a logótipos com várias estruturas.");
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
  const scaleMarkersSwitch = dimGrp.addSwitch("Scale Markers to Object", true);

  // Por defeito, usa dimensionamento automático para evitar aglomeração de pontos.
  const handleScalingCombo = dimGrp.addComboBox("Handle Scaling", ["Automatic (Smart Damping)", "Fixed (Strict Dot Size)"], 0);
  const stemScaleCombo = dimGrp.addComboBox("Handle Stem Projection", ["1.0x (Exact Tangent)", "1.5x (Extended)", "2.0x (Bold Projection)", "3.0x (Technical Guide)"], 0);

  const markerStyleOptions = ["Fill + Stroke", "Fill Only", "Stroke Only"];
  const anchorStyleCombo = dimGrp.addComboBox("Anchor Style", markerStyleOptions, 0);
  const handleStyleCombo = dimGrp.addComboBox("Handle Style", markerStyleOptions, 0);
  const landmarkStyleCombo = dimGrp.addComboBox("Landmark Style", markerStyleOptions, 2);

  attachTip(anchorSizeCtrl, "Largura dos nós quadrados das âncoras em pixels.");
  attachTip(handleSizeCtrl, "Diâmetro dos pontos circulares nas extremidades dos handles de Bézier.");
  attachTip(landmarkSizeCtrl, "Diâmetro dos marcadores de extremos e eventos de curva.");
  attachTip(scaleMarkersSwitch, "Quando activo, os tamanhos dos marcadores, as distâncias de colisão, a tolerância de fusão e a margem da grelha acompanham a dimensão do objecto. Os valores dos controlos são referências para uma geometria de 600 × 600 unidades de coordenadas.");
  attachTip(handleScalingCombo, "'Automatic' reduz pontos em zonas densas e oculta os que colidiriam; 'Fixed' mantém o diâmetro, com filtragem dos conflitos inevitáveis.");
  attachTip(stemScaleCombo, "Nos valores acima de 1x, a haste e o marcador principal são projectados juntos para a nova extremidade. A geometria Bézier original não é alterada.");
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
      const baseGeometry = analyzeSmartGeometry(polyCurve, anchorSize, handleSize, componentModel);
      baseGeometry.componentModel = componentModel;
      geometryCache[key] = enrichGeometryAnalysis(polyCurve, baseGeometry);
    }
    return geometryCache[key];
  }

  function getDisplayAnchors(geom, mode, gap, effectiveAnchorSize) {
    const source = geom.anchors.slice().sort((a, b) => b.priority - a.priority);
    // O modo "All Anchors" continua a mostrar todos os nós sem filtragem visual.
    if (mode === 1) return source;

    const result = [];
    const threshold = Math.max(Number.EPSILON, mode === 2 ? gap * 1.35 : gap);
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

    const baseHalf = effectiveAnchorSize / 2;
    const nearestDistances = calculateNearestDistances(result, Math.max(Number.EPSILON, effectiveAnchorSize * 2.4));
    return result.map((a, i) => {
      const nearest = nearestDistances[i];
      const halfSize = nearest < effectiveAnchorSize * 2.4
        ? Math.max(baseHalf * 0.12, Math.min(baseHalf, nearest * 0.32))
        : baseHalf;
      return Object.assign({}, a, { halfSize: halfSize, clearance: nearest });
    });
  }

  // =========================================================================
  // MOTOR GEOMÉTRICO RESTAURADO COM CORTES TRANSVERSAIS INTEGRADOS NA GRELHA
  // =========================================================================
  function buildGridStructure() {
    const scaleFactor = scaleMarkersSwitch.value ? initialScaleContext.scaleFactor : 1;
    const effectiveAnchorSize = anchorSizeCtrl.value * scaleFactor;
    const effectiveHandleSize = handleSizeCtrl.value * scaleFactor;
    const effectiveLandmarkSize = landmarkSizeCtrl.value * scaleFactor;
    const effectiveMinGap = minNodeGapCtrl.value * scaleFactor;
    const effectiveMergeDistance = mergeDistCtrl.value * scaleFactor;
    const effectiveGridReach = gridReachCtrl.value * scaleFactor;
    const geom = getCachedGeometry(effectiveAnchorSize, effectiveHandleSize);
    const landmarkCoincidenceTolerance = Math.max(
      Number.EPSILON * 100,
      Math.hypot(geom.bounds.width, geom.bounds.height) * 1e-7
    );
    const minGap = effectiveMinGap;
    const smartCollision = adaptiveScaleSwitch.value;
    const isHandleFixed = handleScalingCombo.selectedIndex === 1;

    let displayAnchors = getDisplayAnchors(geom, nodeDisplayCombo.selectedIndex, minGap, effectiveAnchorSize);
    // Construction analysis always uses the complete, unfiltered geometry.
    // These collections are independent from whether marker layers are visible.
    const constructionAnchors = geom.anchors;
    const constructionLandmarks = geom.landmarks;
    let displayHandles = geom.handles;

    const stemMultipliers = [1.0, 1.5, 2.0, 3.0];
    const stemMultiplier = stemMultipliers[stemScaleCombo.selectedIndex] || 1.0;

    if (!smartCollision) {
      const baseHalf = effectiveAnchorSize / 2;
      displayAnchors = displayAnchors.map(a => Object.assign({}, a, { halfSize: baseHalf }));
    }

    if (isHandleFixed) {
      const baseDot = effectiveHandleSize / 2;
      displayHandles = displayHandles.map(h => Object.assign({}, h, { dotRadius: baseDot }));
    }

    const projectedHandles = projectHandlePositions(displayHandles, stemMultiplier);

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
        handleObstacles.push({ x: l.x, y: l.y, halfSize: effectiveLandmarkSize / 2 });
      }
    }
    if (showInflectionSwitch.value) {
      for (const l of geom.landmarks) {
        if (l.type === "inflection") {
          handleObstacles.push({ x: l.x, y: l.y, halfSize: effectiveHandleSize * 0.35 });
        }
      }
    }
    const visualHandles = smartCollision
      ? buildCollisionSafeHandles(projectedHandles, handleObstacles, effectiveHandleSize, !isHandleFixed)
      : projectedHandles;

    const exactBounds = initialExactBounds || geom.bounds;
    const exactCenter = {
      x: exactBounds.x + exactBounds.width / 2,
      y: exactBounds.y + exactBounds.height / 2
    };
    const preserveRadialBounds = gridModeCombo.selectedIndex === 1 && geom.isRadialArray;
    const framingBounds = preserveRadialBounds ? geom.bounds : exactBounds;
    const constructionBounds = reachModeCombo.selectedIndex === 0
      ? { x: framingBounds.x - effectiveGridReach, y: framingBounds.y - effectiveGridReach, width: framingBounds.width + effectiveGridReach * 2, height: framingBounds.height + effectiveGridReach * 2 }
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
    // Use the centre/radius representatives produced by refineCircleCandidates,
    // not every independently fitted Bézier segment.
    const visibleCircles = geom.displayCircles || [];
    if (showCirclesSwitch.value && visibleCircles.length > 0) {
      const defsArcs = [];
      for (const c of visibleCircles) {
        defsArcs.push(PolyCurveNodeDefinition.create(makeSmoothCirclePoly(c.cx, c.cy, c.r), noFill, outlineStroke, lsdOutline, noFill));
      }
      subContainers.push({ name: "2. Curvature Arcs & Rings", defs: defsArcs });
    }

    // 3. Construction Gridlines
    if (showGridSwitch.value && constructionAnchors.length > 0) {
      const defs = [];
      const gridMode = gridModeCombo.selectedIndex;
      const profileIds = ["geometric","typographic","handwriting","organic","radial"];
      const selectedProfile = analysisProfileCombo.selectedIndex === 0
        ? geom.profile.suggested
        : profileIds[analysisProfileCombo.selectedIndex - 1] || geom.profile.suggested;

      // Radial construction is only enabled when the selected/detected profile
      // agrees with a positively detected radial topology.
      if (geom.isRadialArray &&
          (gridMode === 1 || (gridMode === 0 && selectedProfile === "radial"))) {
        const innerPetals = geom.innerBand;
        const outerPetals = geom.outerBand;
        const minR = innerPetals.reduce((m, p) => Math.min(m, p.rIn), Infinity);
        const centerVoidLimit = Math.max(initialScaleContext.diagonal * 0.012, minR * 0.72);

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
              const radialClearance = initialScaleContext.diagonal * 0.006;
              const backSpan = (dToInner < radialClearance * 1.25) ? 0 : Math.min(edge.len * 0.18, Math.max(0, dToInner - radialClearance));
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
              const radialClearance = initialScaleContext.diagonal * 0.006;
              const maxForwardSpan = initialScaleContext.diagonal * 0.02;
              const forwardSpan = isFinite(dToOuter) ? Math.max(0, Math.min(maxForwardSpan, dToOuter - radialClearance)) : Math.min(maxForwardSpan, edge.len * 0.6);
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
            const desiredSpan = clamp(cap.len * 0.55, initialScaleContext.diagonal * 0.012, initialScaleContext.diagonal * 0.024);
            let deltaA = desiredSpan;
            let deltaB = desiredSpan;

            // Proteção analítica: se outra pétala estiver próxima, limita para não invadir o corpo vizinho
            for (const otherPetal of geom.petalData) {
              if (otherPetal !== petal) {
                for (const opt of otherPetal.pts) {
                  const dA = dist(cap.p1, opt);
                  const radialClearance = initialScaleContext.diagonal * 0.006;
                  if (dA < desiredSpan + radialClearance) deltaA = Math.min(deltaA, Math.max(0, dA - radialClearance));

                  const dB = dist(cap.p2, opt);
                  const radialClearanceB = initialScaleContext.diagonal * 0.006;
                  if (dB < desiredSpan + radialClearanceB) deltaB = Math.min(deltaB, Math.max(0, dB - radialClearanceB));
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
        const alignmentPoints = constructionAnchors.map(anchor => Object.assign({}, anchor, {
          alignmentKind: "anchor",
          importance: anchor.importance || anchor.priority || 30
        }));
        for (const landmark of constructionLandmarks) {
          alignmentPoints.push(Object.assign({}, landmark, {
            alignmentKind: "landmark",
            importance: landmark.importance || (landmark.type === "extrema" ? 70 : 45)
          }));
        }

        const preciseAngle = initialPreciseAngle;
        const geometryDiagonal = Math.max(Number.EPSILON * 100, Math.hypot(exactBounds.width, exactBounds.height));
        const minorGeometrySpan = Math.max(
          Number.EPSILON * 100,
          Math.min(Math.abs(exactBounds.width), Math.abs(exactBounds.height))
        );
        const alignmentTolerance = Math.max(
          Math.min(geometryDiagonal * 0.0015, minorGeometrySpan * 0.025),
          Math.min(effectiveMergeDistance * 0.18, minorGeometrySpan * 0.025)
        );
        // Only measured straight-edge families become long construction axes.
        // Curve tangents remain local Bézier evidence and must not dictate a
        // page-wide grid direction on rounded or organic lettering.
        const directionFamilies = (geom.directionFamilies || [])
          .filter(family =>
            family.confidence >= 0.58 &&
            family.share >= 0.085 &&
            family.supportCount >= 2
          )
          .slice(0, 4);
        const profileAlignmentPoints = selectedProfile === "typographic"
          ? alignmentPoints.filter(point => point.alignmentKind === "anchor")
          : alignmentPoints;
        const constructionSymmetry = constructionAnchors.length >= 3
          ? detectAxisSymmetry(constructionAnchors, preciseAngle)
          : { score: 0, axis: preciseAngle };
        const constructionModules = geom.modules || { axes: [], confidence: 0 };
        const anchorMatchTolerance = Math.max(geometryDiagonal * 0.0005, 0.35);
        function hasConstructionAnchorAt(point) {
          return constructionAnchors.some(anchor => dist(anchor, point) <= anchorMatchTolerance);
        }

        if (gridMode === 0) {
          // Each profile limits which directions may become full-frame guides.
          let selectedFamilies = directionFamilies.slice(0, 3);
          if (selectedProfile === "handwriting") {
            selectedFamilies = directionFamilies.filter(f => f.straightSupport > 0 && f.share >= 0.16).slice(0, 1);
          } else if (selectedProfile === "organic") {
            selectedFamilies = directionFamilies.filter(f => f.straightSupport > 0 && f.confidence >= 0.62 && f.share >= 0.13).slice(0, 1);
          } else if (selectedProfile === "typographic") {
            selectedFamilies = directionFamilies.slice(0, 2);
          }
          if (selectedFamilies.length) {
            selectedFamilies.forEach((family, index) => {
              const familyBoost = Math.min(10, (family.confidence || 0) * 10);
              addAlignmentLineCandidates(
                profileAlignmentPoints, gridOrigin, family.angle, alignmentTolerance,
                candidates, (selectedProfile === "typographic" ? 42 : 30) + familyBoost - index * 2.5, "direction-family-alignment"
              );
              // Handwriting and organic forms do not inherit a perpendicular lattice.
              if (selectedProfile !== "handwriting" && selectedProfile !== "organic") {
                addAlignmentLineCandidates(
                  profileAlignmentPoints, gridOrigin, family.angle + Math.PI / 2, alignmentTolerance,
                  candidates, (selectedProfile === "typographic" ? 38 : 25) + familyBoost - index * 2.5, "direction-family-perpendicular"
                );
              }
            });
          }

          // Preserve substantial straight edges. Very short edges often belong
          // to local contour details and should not become full-frame diagonals.
          const minGuideEdge = Math.max(6, Math.hypot(exactBounds.width, exactBounds.height) * 0.045);
          for (const seg of geom.straightSegments) {
            if (dist(seg.p1, seg.p2) < minGuideEdge) continue;
            if (!hasConstructionAnchorAt(seg.p1) || !hasConstructionAnchorAt(seg.p2)) continue;
            candidates.push({ p1: seg.p1, p2: seg.p2, angle: seg.angle, finiteSegment:true, importance: 82, support: 1, source: "structural-edge" });
          }
        } else if (gridMode === 2) {
          // Orthogonal grid: cluster all real nodes and curve landmarks, not only
          // the anchors currently visible in the marker layer.
          addAlignmentLineCandidates(alignmentPoints, gridOrigin, 0, alignmentTolerance, candidates, 38, "horizontal-alignment", 2);
          addAlignmentLineCandidates(alignmentPoints, gridOrigin, Math.PI / 2, alignmentTolerance, candidates, 38, "vertical-alignment", 2);
        } else {
          // Structural Edges: keep actual straight segments and avoid fabricating
          // diagonal chords across curved portions of the logo.
          for (const seg of geom.straightSegments) {
            if (!hasConstructionAnchorAt(seg.p1) || !hasConstructionAnchorAt(seg.p2)) continue;
            candidates.push({ p1: seg.p1, p2: seg.p2, angle: seg.angle, finiteSegment:true, importance: 86, support: 1, source: "structural-edge" });
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
          }
        }

        // Local Bézier tangents are opt-in. They are not global construction axes
        // by default: otherwise every curve extremum can project an arbitrary
        // full-frame line and overwhelm the structural grid.
        const tangentMode = tangentSourceCombo.selectedIndex;
        if (tangentMode >= 1 && geom.handles.length > 0) {
          addBezierTangentCandidates(polyCurve, geom.handles, candidates, tangentMode === 2);
        }

        // Curvature centres create useful cross-axes, while the actual circles
        // remain in their independent layer.
        if (showModulesSwitch.value && geom.circleFamilies && geom.circleFamilies.length > 0) {
          for (const family of geom.circleFamilies) {
            addCircleFamilyConstructionCandidates([family], candidates, {
              maxFamilies:1,
              minConfidence:0.78,
              importance:62,
              componentId:family.componentId
            });
          }
        }

        // Component-scoped circle families above are the single source for
        // circular construction axes; do not add a second local copy.

        if (showSymmetrySwitch.value && constructionSymmetry.score >= 0.70) {
          candidates.push({
            p1: exactCenter,
            angle: constructionSymmetry.axis,
            importance: 100,
            source: "symmetry-axis"
          });
        }

        if (showModulesSwitch.value && selectedProfile !== "handwriting" &&
            constructionAnchors.length >= 4 && constructionModules.axes && constructionModules.axes.length) {
          for (const axis of constructionModules.axes.slice(0, 2)) {
            createModuleGridCandidates(axis, exactBounds, exactCenter, candidates, alignmentTolerance);
          }

          // Component-level lattices remain local to their own glyph/shape.
          // Only strong repeated spacing with sufficient independent anchors is promoted.
          const localModuleComponents = (geom.componentAnalysis || [])
            .filter(component => component.localAnchorCount >= 6 &&
              component.localModules && component.localModules.axes &&
              component.localModules.axes.length &&
              component.localModules.axes[0].confidence >= 0.82 &&
              component.localModules.axes[0].pointCount >= 6)
            .sort((a,b) => b.localModules.axes[0].confidence - a.localModules.axes[0].confidence)
            .slice(0,3);

          for (const component of localModuleComponents) {
            const bounds = component.bounds;
            if (!bounds || !(bounds.width > 0) || !(bounds.height > 0)) continue;
            const centre = { x: bounds.x + bounds.width / 2, y: bounds.y + bounds.height / 2 };
            createModuleGridCandidates(
              component.localModules.axes[0], bounds, centre, candidates,
              alignmentTolerance,
              {
                maxLines:3,
                importance:61,
                source:"component-modular-grid",
                componentId:component.id,
                scopeKey:"component:"+component.id,
                clipBounds:bounds
              }
            );
          }
        }

        if (gridMode === 0 && candidates.length === 0) {
          addFallbackCurveGuideCandidates(polyCurve, geom.handles, candidates, exactBounds, 4);
        }

        const cleanLines = buildCollisionSafeLines(
          candidates,
          {
            anchors: constructionAnchors,
            handles: geom.handles,
            points: constructionLandmarks
          },
          effectiveMergeDistance,
          exactBounds
        );

        // Keep the strongest and best-supported guides; duplicate filtering is
        // geometric, not based on how many anchors a valid line happens to cross.
        // Merge tolerance also provides a restrained detail control: larger
        // values remove near-duplicate candidates and lower the guide budget.
        const detailFactor = clamp(1.18 - mergeDistCtrl.value * 0.0062, 0.56, 1.12);
        const profileBudget = selectedProfile === "handwriting" ? 9 : (selectedProfile === "organic" ? 12 : (selectedProfile === "typographic" ? 24 : 20));
        const baseGuideBudget = gridMode === 2 ? 28 : (gridMode === 3 ? 22 : profileBudget);
        const guideBudget = Math.max(10, Math.round(baseGuideBudget * detailFactor));
        const renderedGuideSegments = [];
        for (const line of cleanLines) {
          const clipBounds = line.clipBounds ||
            ((line.source === "bounding-box-edge" || line.source === "bounding-box-diagonal")
              ? exactBounds
              : constructionBounds);
          const ext = extendLineToRect(line, clipBounds);
          if (!ext || dist(ext.p1, ext.p2) <= Number.EPSILON * 100) continue;
          renderedGuideSegments.push({ line, ext });
        }

        // Consolidate overlapping line segments after clipping, including lines
        // that came from different sources or component scopes.
        let uniqueRenderedGuides = mergeCoincidentRenderedLines(
          renderedGuideSegments,
          effectiveMergeDistance,
          exactBounds
        );

        // Protect the final rendering stage as well: a non-empty candidate set
        // can still disappear after clipping or coincidence consolidation.
        if (gridMode === 0 && uniqueRenderedGuides.length === 0) {
          const fallbackCandidates = [];
          addFallbackCurveGuideCandidates(polyCurve, geom.handles, fallbackCandidates, exactBounds, 4);
          if (fallbackCandidates.length) {
            const fallbackLines = buildCollisionSafeLines(
              fallbackCandidates,
              { anchors: constructionAnchors, handles: geom.handles, points: constructionLandmarks },
              effectiveMergeDistance,
              exactBounds
            );
            const fallbackRendered = [];
            for (const line of fallbackLines) {
              const ext = extendLineToRect(line, line.clipBounds || constructionBounds);
              if (ext && dist(ext.p1, ext.p2) > Number.EPSILON * 100) {
                fallbackRendered.push({ line, ext });
              }
            }
            uniqueRenderedGuides = mergeCoincidentRenderedLines(
              fallbackRendered,
              effectiveMergeDistance,
              exactBounds
            );
          }
        }

        for (const item of uniqueRenderedGuides.slice(0, guideBudget)) {
          appendStyledGridLine(defs, item.line, item.ext, gridStrokeStyles, noFill);
        }


      }
      if (defs.length) subContainers.push({ name: "3. Construction Gridlines", defs: defs });
    }

    // 4. Geometric Landmarks
    // Only derived curve events are shown here. Native path vertices remain
    // exclusively in Anchor Nodes, avoiding a second marker over the same node.
    if (showLandmarksSwitch.value) {
      const defs = [];
      const baseLandmarkR = effectiveLandmarkSize / 2;
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
      const baseInflectR = effectiveHandleSize * 0.35;
      const defs = geom.landmarks.filter(l => l.type === "inflection").map(l => PolyCurveNodeDefinition.create(makeSmoothCirclePoly(l.x, l.y, baseInflectR), landmarkFillDesc, landmarkStrokeDesc, lsdNode, noFill));
      if (defs.length) subContainers.push({ name: "5. Inflection Points", defs: defs });
    }

    // 6-8. Bézier handle projection.
    if (showHandlesSwitch.value && visualHandles.length > 0) {
      const defsStems = [], defsDots = [];
      for (const h of visualHandles) {
        const dx = h.handle.x - h.anchor.x;
        const dy = h.handle.y - h.anchor.y;
        const d = Math.hypot(dx, dy);
        if (d <= EPS) continue;

        const ux = dx / d, uy = dy / d;
        const dotRadius = Math.max(Number.EPSILON * 100, h.dotRadius);

        if (d > dotRadius * 1.08) {
          defsStems.push(PolyCurveNodeDefinition.create(
            makeLinePoly(
              h.anchor.x, h.anchor.y,
              h.handle.x - ux * dotRadius,
              h.handle.y - uy * dotRadius
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
    analysisProfileCombo, gridModeCombo, nodeDisplayCombo, reachModeCombo, tangentSourceCombo, anchorStyleCombo,
    handleStyleCombo, landmarkStyleCombo, stemScaleCombo, handleScalingCombo
  ].forEach(c => {
    try { c.setOnValueChangedHandler(() => render(true)); } catch (e) {}
  });

  [
    showOverlaySwitch, showOutlineSwitch, showCirclesSwitch, showGridSwitch, showHandlesSwitch,
    showAnchorsSwitch, adaptiveScaleSwitch, scaleMarkersSwitch, showSymmetrySwitch,
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