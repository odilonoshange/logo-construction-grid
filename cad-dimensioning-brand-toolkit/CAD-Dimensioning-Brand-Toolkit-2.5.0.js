
/**
 * name: CAD Dimensioning — Brand Toolkit
 * version: 2.5.0 — Editorial Logo Study Output
 */
"use strict";

const { Document } = require("/document.js");
const { Dialog, DialogResult } = require("/dialog.js");
const { UnitType } = require("/units.js");
const { DocumentCommand, AddChildNodesCommandBuilder, InsertionMode, NodeChildType } = require("/commands.js");
const { Selection } = require("/selections.js");
const { PolyCurve, CurveBuilder } = require("/geometry.js");
const { PolyCurveNodeDefinition, ContainerNodeDefinition, ArtTextNodeDefinition } = require("/nodes.js");
const { FillDescriptor } = require("/fills.js");
const { LineStyleDescriptor } = require("/linestyle.js");
const { Colour } = require("/colours.js");
const { StoryBuilder } = require("/storybuilder.js");
const { StoryDelta } = require("/storydelta.js");

const doc = Document.current;
const EPS = 1e-7;

// Affinity's official Crop Marks tutorial uses this constructor for strokes.
// Keep the same direct descriptor creation used by the original script.
function createWeightedStroke(weight) {
  const w = Math.max(0.01, Number(weight) || 0.1);
  return LineStyleDescriptor.createDefault(w);
}

function attachTip(ctrl, text) {
  if (!ctrl || !text) return;
  // In Affinity SDK 3.3, the supported tooltip property is 'description'
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

function isEmbedded(node) {
  try {
    return !!node && (
      node.isEmbeddedDocumentNode ||
      node[Symbol.toStringTag] === "EmbeddedDocumentNode" ||
      !!node.embeddedDocumentInterface
    );
  } catch (e) {
    return false;
  }
}

function toArray(v) {
  if (!v) return [];
  if (Array.isArray(v)) return v;
  try { if (v.toArray) return v.toArray(); } catch (e) {}
  try { return Array.from(v); } catch (e) {}
  return [];
}

function collectBeziers(curve) {
  const beziers = [];
  try {
    for (const bez of curve.beziers) beziers.push(bez);
  } catch (e) {}
  return beziers;
}

function extractPolyCurvesFromSingleNode(node) {
  try {
    const ci = node.curvesInterface;
    if (!ci || !ci.polyCurve || ci.polyCurve.curveCount === 0) return null;
    const pc = ci.polyCurve.clone();
    pc.transform(node.baseToSpreadTransform);
    return pc;
  } catch (e) {
    return null;
  }
}

function collectDeepPolyCurves(rootNodes) {
  const result = [];
  function traverse(node) {
    if (!node || isEmbedded(node)) return;
    const pc = extractPolyCurvesFromSingleNode(node);
    if (pc && pc.curveCount > 0) {
      result.push(pc);
      return;
    }
    for (const child of toArray(node.children)) traverse(child);
  }
  for (const n of rootNodes) traverse(n);
  return result;
}

function solveQuadratic(a, b, c) {
  if (![a, b, c].every(Number.isFinite)) return [];
  const scale = Math.max(Math.abs(a), Math.abs(b), Math.abs(c));
  if (scale === 0) return [];
  a /= scale; b /= scale; c /= scale;
  const tol = Number.EPSILON * 64;
  if (Math.abs(a) <= tol) {
    if (Math.abs(b) <= tol) return [];
    const t = -c / b;
    return Number.isFinite(t) && t > EPS && t < 1 - EPS ? [t] : [];
  }
  let disc = b * b - 4 * a * c;
  const discTol = Number.EPSILON * 64 * Math.max(b * b, Math.abs(4 * a * c), Number.MIN_VALUE);
  if (disc < -discTol) return [];
  if (Math.abs(disc) <= discTol) {
    const t = -b / (2 * a);
    return Number.isFinite(t) && t > EPS && t < 1 - EPS ? [t] : [];
  }
  disc = Math.sqrt(Math.max(0, disc));
  const q = -0.5 * (b + (b < 0 ? -disc : disc));
  const candidates = [q / a, Math.abs(q) > tol ? c / q : -b / (2 * a)];
  const roots = [];
  for (const t of candidates) {
    if (Number.isFinite(t) && t > EPS && t < 1 - EPS && !roots.some(r => Math.abs(r - t) < 1e-10)) roots.push(t);
  }
  return roots.sort((x, y) => x - y);
}

function cubicPoint(b, t) {
  const mt = 1 - t;
  const mt2 = mt * mt;
  const t2 = t * t;
  return {
    x: mt2 * mt * b.start.x + 3 * mt2 * t * b.c1.x + 3 * mt * t2 * b.c2.x + t2 * t * b.end.x,
    y: mt2 * mt * b.start.y + 3 * mt2 * t * b.c1.y + 3 * mt * t2 * b.c2.y + t2 * t * b.end.y
  };
}

function computeExactCurveBounds(curve) {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const b of collectBeziers(curve)) {
    minX = Math.min(minX, b.start.x, b.end.x);
    minY = Math.min(minY, b.start.y, b.end.y);
    maxX = Math.max(maxX, b.start.x, b.end.x);
    maxY = Math.max(maxY, b.start.y, b.end.y);

    const ax = -b.start.x + 3 * b.c1.x - 3 * b.c2.x + b.end.x;
    const bx = b.start.x - 2 * b.c1.x + b.c2.x;
    const cx = b.c1.x - b.start.x;
    for (const t of solveQuadratic(ax, 2 * bx, cx)) {
      const p = cubicPoint(b, t);
      minX = Math.min(minX, p.x);
      maxX = Math.max(maxX, p.x);
    }

    const ay = -b.start.y + 3 * b.c1.y - 3 * b.c2.y + b.end.y;
    const by = b.start.y - 2 * b.c1.y + b.c2.y;
    const cy = b.c1.y - b.start.y;
    for (const t of solveQuadratic(ay, 2 * by, cy)) {
      const p = cubicPoint(b, t);
      minY = Math.min(minY, p.y);
      maxY = Math.max(maxY, p.y);
    }
  }

  return isFinite(minX) ? {
    x: minX,
    y: minY,
    width: maxX - minX,
    height: maxY - minY,
    cx: (minX + maxX) / 2,
    cy: (minY + maxY) / 2
  } : null;
}

function extractAllGeometricVertices(polyCurves, tolerance) {
  const pts = [];
  const tol = Math.max(EPS, tolerance || 1.0);

  const addUnique = pt => {
    if (!pt || !Number.isFinite(pt.x) || !Number.isFinite(pt.y)) return;
    if (!pts.some(p => Math.hypot(p.x - pt.x, p.y - pt.y) < tol)) {
      pts.push({ x: pt.x, y: pt.y });
    }
  };

  for (const pc of polyCurves) {
    for (let c = 0; c < pc.curveCount; c++) {
      const beziers = collectBeziers(pc.at(c));
      for (const bez of beziers) {
        // Real path anchors.
        addUnique(bez.start);
        addUnique(bez.end);

        // Add true cubic extrema. These are useful dimension landmarks even
        // when the visual extreme falls between editable Bézier nodes.
        const ax = -bez.start.x + 3 * bez.c1.x - 3 * bez.c2.x + bez.end.x;
        const bx = bez.start.x - 2 * bez.c1.x + bez.c2.x;
        const cx = bez.c1.x - bez.start.x;
        for (const t of solveQuadratic(ax, 2 * bx, cx)) addUnique(cubicPoint(bez, t));

        const ay = -bez.start.y + 3 * bez.c1.y - 3 * bez.c2.y + bez.end.y;
        const by = bez.start.y - 2 * bez.c1.y + bez.c2.y;
        const cy = bez.c1.y - bez.start.y;
        for (const t of solveQuadratic(ay, 2 * by, cy)) addUnique(cubicPoint(bez, t));
      }
    }
  }
  return pts;
}

function appendPolyCurve(target, source) {
  if (!target || !source) return;
  try {
    for (let i = 0; i < source.curveCount; i++) {
      target.addCurve(source.at(i).clone());
    }
  } catch (e) {}
}

function getFeatureLandmarks(points, bounds, axis, side, detailLevel) {
  const horizontal = axis === "x";
  const axisKey = horizontal ? "x" : "y";
  const crossKey = horizontal ? "y" : "x";
  const isMinimum = side === "top" || side === "left";
  const extent = horizontal ? bounds.width : bounds.height;
  const minDim = Math.min(bounds.width, bounds.height);

  const clusterFactor = [0.016, 0.009, 0.004][detailLevel] || 0.016;
  const separationFactor = [0.085, 0.060, 0.035][detailLevel] || 0.085;
  const prominenceFactor = [0.045, 0.028, 0.015][detailLevel] || 0.045;
  const clusterTol = Math.max(EPS * 10, minDim * clusterFactor);
  const minSeparation = Math.max(clusterTol * 2, extent * separationFactor);
  const minProminence = Math.max(EPS * 10, minDim * prominenceFactor);

  let region;
  if (side === "top") region = points.filter(p => p.y <= bounds.y + bounds.height * 0.44);
  else if (side === "bottom") region = points.filter(p => p.y >= bounds.y + bounds.height * 0.56);
  else if (side === "left") region = points.filter(p => p.x <= bounds.x + bounds.width * 0.44);
  else region = points.filter(p => p.x >= bounds.x + bounds.width * 0.56);

  region.sort((a, b) => a[axisKey] - b[axisKey]);
  if (region.length < 2) return { side, axis, anchors: [], spans: [], score: 0 };

  // Collapse nearby anchors that describe the same geometric feature. Keep
  // the point closest to the selected silhouette side, not the first point.
  const clusters = [];
  for (const point of region) {
    let cluster = clusters.length ? clusters[clusters.length - 1] : null;
    if (!cluster || Math.abs(point[axisKey] - cluster.axisMean) > clusterTol) {
      cluster = { points: [point], axisMean: point[axisKey] };
      clusters.push(cluster);
    } else {
      cluster.points.push(point);
      cluster.axisMean = cluster.points.reduce((sum, p) => sum + p[axisKey], 0) / cluster.points.length;
    }
  }

  const representatives = clusters.map(cluster => {
    let best = cluster.points[0];
    for (const point of cluster.points) {
      if (isMinimum ? point[crossKey] < best[crossKey] : point[crossKey] > best[crossKey]) best = point;
    }
    return { x: best.x, y: best.y, prominence: 0 };
  }).sort((a, b) => a[axisKey] - b[axisKey]);

  if (representatives.length < 2) return { side, axis, anchors: [], spans: [], score: 0 };

  // Outer landmarks are useful references. Interior landmarks are retained
  // only when they form a meaningful peak or valley in the silhouette.
  const candidates = [
    { ...representatives[0], edge: true },
    { ...representatives[representatives.length - 1], edge: true }
  ];

  for (let i = 1; i < representatives.length - 1; i++) {
    const prev = representatives[i - 1];
    const current = representatives[i];
    const next = representatives[i + 1];
    const before = isMinimum
      ? prev[crossKey] - current[crossKey]
      : current[crossKey] - prev[crossKey];
    const after = isMinimum
      ? next[crossKey] - current[crossKey]
      : current[crossKey] - next[crossKey];
    const prominence = Math.min(before, after);
    if (before > 0 && after > 0 && prominence >= minProminence) {
      candidates.push({ ...current, prominence, edge: false });
    }
  }

  candidates.sort((a, b) => a[axisKey] - b[axisKey]);

  // Prevent tiny adjacent spans. If two landmarks are too close, preserve the
  // more distinctive one unless one of them is an outer endpoint.
  const selected = [];
  for (const candidate of candidates) {
    if (!selected.length) {
      selected.push(candidate);
      continue;
    }
    const previous = selected[selected.length - 1];
    if (candidate[axisKey] - previous[axisKey] < minSeparation) {
      if (previous.edge && !candidate.edge) continue;
      if (!previous.edge && candidate.edge) selected[selected.length - 1] = candidate;
      else if (candidate.prominence > previous.prominence) selected[selected.length - 1] = candidate;
    } else {
      selected.push(candidate);
    }
  }

  // Keep a restrained, user-controlled maximum: major detail stays compact,
  // while balanced and dense modes can expose more internal landmarks.
  const maxAnchors = [4, 5, 7][detailLevel] || 4;
  if (selected.length > maxAnchors) {
    const first = selected[0];
    const last = selected[selected.length - 1];
    const inner = selected.slice(1, -1)
      .sort((a, b) => b.prominence - a.prominence)
      .slice(0, maxAnchors - 2)
      .sort((a, b) => a[axisKey] - b[axisKey]);
    selected.length = 0;
    selected.push(first, ...inner, last);
  }

  const spans = [];
  const minSpan = extent * [0.10, 0.075, 0.045][detailLevel];
  // A pair of outer points alone is not an internal feature. Requiring at
  // least one interior landmark prevents circles and smooth ovals from being
  // mistaken for shapes with several meaningful feature spans.
  if (selected.length >= 3) for (let i = 0; i < selected.length - 1; i++) {
    const a = selected[i];
    const b = selected[i + 1];
    const length = Math.abs(b[axisKey] - a[axisKey]);
    if (length < minSpan || length > extent * 0.93) continue;
    spans.push({ a, b, length, index: i, prominence: Math.max(a.prominence || 0, b.prominence || 0) });
  }

  // Prefer spans that reveal a real feature, while retaining left-to-right or
  // top-to-bottom ordering in the final drawing.
  const maxSpans = [2, 3, 5][detailLevel] || 2;
  const chosenSpans = spans
    .sort((a, b) => (b.length + b.prominence * 1.5) - (a.length + a.prominence * 1.5))
    .slice(0, maxSpans)
    .sort((a, b) => a.index - b.index);

  const range = Math.abs(selected[selected.length - 1][axisKey] - selected[0][axisKey]);
  const totalProminence = selected.reduce((sum, p) => sum + (p.prominence || 0), 0);
  const score = chosenSpans.length * 4 + range / Math.max(EPS, extent) + totalProminence / Math.max(EPS, minDim);

  return { side, axis, anchors: selected, spans: chosenSpans, score };
}

function findBestFeatureLandmarks(points, bounds, detailLevel) {
  const candidates = [
    getFeatureLandmarks(points, bounds, "x", "top", detailLevel),
    getFeatureLandmarks(points, bounds, "x", "bottom", detailLevel),
    getFeatureLandmarks(points, bounds, "y", "left", detailLevel),
    getFeatureLandmarks(points, bounds, "y", "right", detailLevel)
  ].filter(item => item.spans.length > 0);

  candidates.sort((a, b) => b.score - a.score);
  return candidates.length ? candidates[0] : null;
}

function makeLinePolyCurve(x1, y1, x2, y2) {
  const cb = CurveBuilder.create();
  cb.beginXY(x1, y1);
  cb.lineToXY(x2, y2);
  const pc = PolyCurve.create();
  pc.addCurve(cb.createCurve());
  return pc;
}

function makeRoundedRectPolyCurve(x, y, width, height, radius) {
  const r = Math.max(0, Math.min(Number(radius) || 0, width / 2, height / 2));
  const k = 0.5522847498;
  const b = CurveBuilder.create().beginXY(x + r, y);

  if (width - 2 * r > EPS) b.lineToXY(x + width - r, y);
  if (r > 0) b.addBezierXY(x + width - r * (1 - k), y, x + width, y + r * (1 - k), x + width, y + r);
  if (height - 2 * r > EPS) b.lineToXY(x + width, y + height - r);
  if (r > 0) b.addBezierXY(x + width, y + height - r * (1 - k), x + width - r * (1 - k), y + height, x + width - r, y + height);
  if (width - 2 * r > EPS) b.lineToXY(x + r, y + height);
  if (r > 0) b.addBezierXY(x + r * (1 - k), y + height, x, y + height - r * (1 - k), x, y + height - r);
  if (height - 2 * r > EPS) b.lineToXY(x, y + r);
  if (r > 0) b.addBezierXY(x, y + r * (1 - k), x + r * (1 - k), y, x + r, y);

  const pc = PolyCurve.create();
  pc.addCurve(b.close().createCurve());
  return pc;
}

function createFilledPanelDef(curve, colourObj) {
  return PolyCurveNodeDefinition.create(
    curve,
    FillDescriptor.createSolid(colourObj),
    FillDescriptor.createNone(),
    LineStyleDescriptor.createDefault(0.1),
    FillDescriptor.createNone()
  );
}

function makeDottedLinePoly(x1, y1, x2, y2, dotLen, gapLen) {
  const pc = PolyCurve.create();
  const d = dotLen || 2;
  const g = gapLen || 4;
  const len = Math.hypot(x2 - x1, y2 - y1);
  if (len < 0.01) return pc;
  const ux = (x2 - x1) / len;
  const uy = (y2 - y1) / len;
  let cur = 0;
  while (cur < len) {
    const segEnd = Math.min(cur + d, len);
    const cb = CurveBuilder.create();
    cb.beginXY(x1 + ux * cur, y1 + uy * cur);
    cb.lineToXY(x1 + ux * segEnd, y1 + uy * segEnd);
    pc.addCurve(cb.createCurve());
    cur += d + g;
  }
  return pc;
}

function formatValueString(valInPoints, unitIndex, precision, baseUnitPx, useComma) {
  let str = "";
  if (unitIndex === 0) {
    const xVal = valInPoints / Math.max(0.1, baseUnitPx);
    str = xVal.toFixed(precision);
    if (precision > 0) {
      str = str.replace(/0+$/, '').replace(/\.$/, '');
    }
    if (useComma) str = str.replace('.', ',');
    return str + "x";
  } else if (unitIndex === 1) {
    str = (valInPoints * (96 / 72)).toFixed(precision) + " px";
  } else if (unitIndex === 2) {
    str = (valInPoints * (25.4 / 72)).toFixed(precision) + " mm";
  } else if (unitIndex === 3) {
    str = (valInPoints * (2.54 / 72)).toFixed(precision) + " cm";
  } else {
    str = (valInPoints / 72).toFixed(precision) + " in";
  }

  if (useComma) str = str.replace('.', ',');
  return str;
}

function createDimensionLabelDef(text, pos, textPt, colourObj, fontFamily) {
  try {
    const sb = StoryBuilder.create();
    try { sb.setToArtisticTextDefaultStyle(doc.dpi, doc.format); } catch (e1) {}
    try {
      const ga = sb.glyphAtts;
      if (ga) {
        ga.height = textPt;
        ga.brushFill = FillDescriptor.createSolid(colourObj);
        sb.setGlyphAtts(ga);
      }
    } catch (e2) {}

    // Apply the family to the label glyphs using the same StoryBuilder API
    // used by Automatic Color Codes. Keep the document default as fallback.
    try {
      if (fontFamily) sb.applyGlyphDelta(StoryDelta.createFamilyName(fontFamily));
    } catch (e3) {}

    sb.addText(text);
    const def = ArtTextNodeDefinition.createFromStoryBuilder({ x: pos.x, y: pos.y }, sb);
    if (def) {
      def.userDescription = "Dim " + text;
      return def;
    }
  } catch (e) {}
  return null;
}

function main() {
  if (!doc || !doc.selection || doc.selection.length === 0) {
    alert("Select a logo or shape to generate dimensions.");
    return;
  }

  const rawSel = toArray(doc.selection.nodes).filter(Boolean);
  if (rawSel.some(isEmbedded)) {
    alert("Embedded documents cannot be measured directly. Convert them to native curves first.");
    return;
  }

  const polyCurves = collectDeepPolyCurves(rawSel);
  if (!polyCurves.length) {
    alert("Could not extract vector geometry from the selection.");
    return;
  }

  // Exact unified bounds from Bézier extrema
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const pc of polyCurves) {
    for (let c = 0; c < pc.curveCount; c++) {
      const b = computeExactCurveBounds(pc.at(c));
      if (b) {
        minX = Math.min(minX, b.x);
        minY = Math.min(minY, b.y);
        maxX = Math.max(maxX, b.x + b.width);
        maxY = Math.max(maxY, b.y + b.height);
      }
    }
  }

  if (![minX, minY, maxX, maxY].every(Number.isFinite) || maxX - minX < EPS || maxY - minY < EPS) {
    alert("The selection has no measurable two-dimensional area. Select a shape with valid width and height.");
    return;
  }
  const bounds = {
    x: minX, y: minY, width: maxX - minX, height: maxY - minY,
    cx: (minX + maxX) / 2, cy: (minY + maxY) / 2
  };
  const vertexTolerance = Math.max(EPS, Math.min(bounds.width, bounds.height) * 0.0005);
  const allVertices = extractAllGeometricVertices(polyCurves, vertexTolerance);

  // Match Automatic Color Codes: enumerate installed font families and pick
  // a sensible default, falling back to Affinity's configured default.
  const { Font, FontFamily } = require("/fonts.js");
  const familyNames = new Set([...FontFamily.all].map(f => f.name));
  const preferredFonts = ["Inter", "Helvetica Neue", "SF Pro Text", "Segoe UI"];
  const defaultFontName = preferredFonts.find(name => familyNames.has(name)) || Font.createDefault().familyName;

  const dlg = Dialog.create("Logo Study — Proportions & Geometry");
  dlg.initialWidth = 620;
  dlg.isResizable = true;

  const colLeft = dlg.addColumn();
  const colRight = dlg.addColumn();

  // --- COLUMN 1: Geometry & Dimension Mode ---
  const modeGrp = colLeft.addGroup("Measurement Focus");
  const dimModeCombo = modeGrp.addComboBox("Style", [
    "Feature Spans",
    "Overall Bounds (Width + Height)",
    "Features + Totals",
    "Four-Sided Enclosure",
    "Horizontal Widths Only",
    "Vertical Heights Only"
  ], 1);
  attachTip(dimModeCombo, "Start with overall width and height. Feature Spans adds only a small number of meaningful silhouette measurements.");

  const featureDetailCombo = modeGrp.addComboBox("Feature Detail", [
    "Major Landmarks",
    "Balanced Landmarks",
    "Dense Landmarks"
  ], 0);
  attachTip(featureDetailCombo, "Controls how many meaningful silhouette features may be dimensioned. It does not blindly measure every node.");

  const unitGrp = colLeft.addGroup("Proportions & Units");
  const unitCombo = unitGrp.addComboBox("Units", [
    "Proportional X Units",
    "Pixels (px)",
    "Millimeters (mm)",
    "Centimeters (cm)",
    "Inches (in)"
  ], 0);
  attachTip(unitCombo, "Use X to represent relative brand proportions.");

  const xRatioTargetCombo = unitGrp.addComboBox("1X Unit Definition", [
    "Total Width = 10x",
    "Total Width = 8x",
    "Total Width = 12x",
    "Total Height = 10x",
    "Custom X (px)"
  ], 0);
  attachTip(xRatioTargetCombo, "Defines the physical distance corresponding to 1X.");

  const customXCtrl = unitGrp.addUnitValueEditor("Custom 1X Value (px)", UnitType.Pixel, doc.units, bounds.width / 10, 1, 5000);
  customXCtrl.showPopupSlider = true;

  const decimalSeparatorCombo = unitGrp.addComboBox("Decimal Separator", [
    "Comma: 11,5x",
    "Period: 11.5x"
  ], 0);

  const precisionCtrl = unitGrp.addUnitValueEditor("Decimal Precision", UnitType.Number, UnitType.Number, 2, 0, 3);
  precisionCtrl.precision = 0;

  // --- COLUMN 2: Dimension Bars, Witness Lines, and Typography ---
  const offsetGrp = colRight.addGroup("Offsets & Clearances");
  const offsetCtrl = offsetGrp.addUnitValueEditor("Primary Offset (px)", UnitType.Pixel, doc.units, 32, 10, 500);
  offsetCtrl.showPopupSlider = true;
  attachTip(offsetCtrl, "Distance from the bounds to the first dimension line.");

  const tierGapCtrl = offsetGrp.addUnitValueEditor("Tier Gap (px)", UnitType.Pixel, doc.units, 22, 5, 200);
  tierGapCtrl.showPopupSlider = true;
  attachTip(tierGapCtrl, "Distance between feature and overall dimension tiers.");

  const anchorGapCtrl = offsetGrp.addUnitValueEditor("Anchor Clearance (px)", UnitType.Pixel, doc.units, 3, 0, 50);
  anchorGapCtrl.showPopupSlider = true;
  attachTip(anchorGapCtrl, "Keeps extension lines from touching the anchor directly.");

  const styleGrp = colRight.addGroup("Brand Sheet Styling");
  const barThicknessCtrl = styleGrp.addUnitValueEditor("Dimension Line Weight (pt)", UnitType.Point, doc.units, 1.2, 0.1, 8);
  barThicknessCtrl.showPopupSlider = true;
  attachTip(barThicknessCtrl, "Controls the primary accent lines. A restrained weight keeps the logo itself as the main focus.");

  const witnessWidthCtrl = styleGrp.addUnitValueEditor("Construction Guide Weight (pt)", UnitType.Point, doc.units, 0.4, 0.05, 4);
  witnessWidthCtrl.showPopupSlider = true;
  attachTip(witnessWidthCtrl, "Controls the lighter guide lines that connect the measured silhouette to its dimensions.");

  const brandColorPicker = styleGrp.addColourPicker("Dimension Accent", Colour.createRGBA8({ r: 235, g: 45, b: 45, alpha: 255 }));
  brandColorPicker.value = Colour.createRGBA8({ r: 235, g: 45, b: 45, alpha: 255 });

  const guideColorPicker = styleGrp.addColourPicker("Construction Guide", Colour.createRGBA8({ r: 137, g: 145, b: 156, alpha: 190 }));
  guideColorPicker.value = Colour.createRGBA8({ r: 137, g: 145, b: 156, alpha: 190 });

  const labelPanelPicker = styleGrp.addColourPicker("Measurement Tag", Colour.createRGBA8({ r: 24, g: 27, b: 32, alpha: 255 }));
  labelPanelPicker.value = Colour.createRGBA8({ r: 24, g: 27, b: 32, alpha: 255 });

  const textGrp = colRight.addGroup("Typography");
  const showTextSwitch = textGrp.addSwitch("Show Labels", true);
  const fontPicker = textGrp.addFontPicker("Font");
  fontPicker.text = defaultFontName;
  attachTip(fontPicker, "Selects the font family used for all dimension labels.");

  const fontSizeCtrl = textGrp.addUnitValueEditor("Text Size (pt)", UnitType.Number, UnitType.Number, 9.5, 4, 36);
  fontSizeCtrl.showPopupSlider = true;

  const textClearanceCtrl = textGrp.addUnitValueEditor("Text Clearance (px)", UnitType.Pixel, doc.units, 8, 0, 50);
  textClearanceCtrl.showPopupSlider = true;

  // Light label text is designed to sit on the dark measurement tags.
  const textColorPicker = textGrp.addColourPicker("Tag Typography", Colour.createRGBA8({ r: 255, g: 255, b: 255, alpha: 255 }));
  textColorPicker.value = Colour.createRGBA8({ r: 255, g: 255, b: 255, alpha: 255 });

  function getBaseUnitPixels() {
    const targetIdx = xRatioTargetCombo.selectedIndex;
    if (targetIdx === 0) return bounds.width / 10;
    if (targetIdx === 1) return bounds.width / 8;
    if (targetIdx === 2) return bounds.width / 12;
    if (targetIdx === 3) return bounds.height / 10;
    return customXCtrl.value;
  }

  function buildCADStructure() {
    const dimMode = dimModeCombo.selectedIndex;
    const detailLevel = featureDetailCombo.selectedIndex;
    const unitIdx = unitCombo.selectedIndex;
    const precision = Math.max(0, Math.floor(precisionCtrl.value));
    const useComma = (decimalSeparatorCombo.selectedIndex === 0);
    const baseUnitPx = getBaseUnitPixels();

    const offset = offsetCtrl.value;
    const tierGap = tierGapCtrl.value;
    const anchorGap = anchorGapCtrl.value;

    const barThickness = barThicknessCtrl.value;
    const witnessWidth = witnessWidthCtrl.value;

    const showText = showTextSwitch.value;
    const selectedFont = (fontPicker.fontFamily && fontPicker.fontFamily.name) || fontPicker.text || defaultFontName;
    const fontSize = fontSizeCtrl.value;
    const textGap = textClearanceCtrl.value;

    // The logo remains the hero. Construction guides are quiet, dimensions
    // use one accent, and values sit in compact editorial tags.
    const effectiveFontSize = fontSize;
    const effectiveTextGap = textGap;

    const brandCol = brandColorPicker.value || Colour.createRGBA8({ r: 235, g: 45, b: 45, alpha: 255 });
    const guideCol = guideColorPicker.value || Colour.createRGBA8({ r: 137, g: 145, b: 156, alpha: 190 });
    const panelCol = labelPanelPicker.value || Colour.createRGBA8({ r: 24, g: 27, b: 32, alpha: 255 });
    const textCol = textColorPicker.value || Colour.createRGBA8({ r: 255, g: 255, b: 255, alpha: 255 });

    const brandStrokeDesc = FillDescriptor.createSolid(brandCol);
    const guideStrokeDesc = FillDescriptor.createSolid(guideCol);
    const noFill = FillDescriptor.createNone();

    // Keep the user-entered weights direct. The lighter guide hierarchy is
    // intentional: annotations should support the mark, not compete with it.
    const lsdBar = createWeightedStroke(barThickness);
    const lsdWitness = createWeightedStroke(witnessWidth);

    // Each element remains a direct node definition, preserving the original
    // non-destructive geometry and predictable layer organisation.
    const extensionDefs = [];
    const dimensionDefs = [];
    const labelPanelDefs = [];
    const textDefs = [];
    const witnessKeys = new Set();

    const addWitnessLine = (vx, vy, targetX, targetY) => {
      const dx = targetX - vx;
      const dy = targetY - vy;
      const len = Math.hypot(dx, dy);
      if (len < 1.0) return;

      const ux = dx / len;
      const uy = dy / len;
      const startX = vx + ux * anchorGap;
      const startY = vy + uy * anchorGap;
      const endX = targetX;
      const endY = targetY;
      const key = [startX, startY, endX, endY].map(v => Math.round(v * 10) / 10).join(":");
      if (witnessKeys.has(key)) return;
      witnessKeys.add(key);

      // Continuous, low-contrast guide lines are more appropriate for a
      // brand-study sheet than drafting-style dotted projections.
      const pc = makeLinePolyCurve(startX, startY, endX, endY);
      const def = PolyCurveNodeDefinition.create(
        pc, noFill, guideStrokeDesc, lsdWitness, noFill
      );
      if (!def) throw new Error("Affinity could not create a construction-guide definition.");
      extensionDefs.push(def);
    };

    const getTagMetrics = (labelText, labelKind) => {
      const captionSize = Math.max(5, effectiveFontSize * 0.58);
      const padX = effectiveFontSize * 0.72;
      const padY = effectiveFontSize * 0.40;
      const rowGap = effectiveFontSize * 0.10;
      const captionWidth = labelKind.length * captionSize * 0.59;
      const valueWidth = labelText.length * effectiveFontSize * 0.56;
      const width = Math.max(captionWidth, valueWidth) + padX * 2;
      const height = padY * 2 + captionSize * 1.10 + rowGap + effectiveFontSize * 1.40;
      return { width, height, captionSize, padX, padY, rowGap };
    };

    const addDimensionLabel = (labelText, x1, y1, x2, y2, isHoriz, labelSide, labelKind) => {
      if (!showText) return;
      const m = getTagMetrics(labelText, labelKind);
      let panelX, panelY;

      if (isHoriz) {
        panelX = (x1 + x2) / 2 - m.width / 2;
        const spanWidth = Math.abs(x2 - x1);
        if (spanWidth > m.width + effectiveFontSize * 0.8) {
          panelY = y1 - m.height / 2;
        } else {
          panelY = labelSide === "below"
            ? y1 + effectiveTextGap
            : y1 - m.height - effectiveTextGap;
        }
      } else {
        panelY = (y1 + y2) / 2 - m.height / 2;
        const connectorGap = Math.max(effectiveTextGap * 0.55, effectiveFontSize * 0.38);
        panelX = labelSide === "left"
          ? x1 - connectorGap - m.width
          : x1 + connectorGap;

        const connectorStart = labelSide === "left" ? panelX + m.width : x1;
        const connectorEnd = labelSide === "left" ? x1 : panelX;
        if (Math.abs(connectorEnd - connectorStart) > 0.5) {
          const connector = PolyCurveNodeDefinition.create(
            makeLinePolyCurve(connectorStart, panelY + m.height / 2, connectorEnd, panelY + m.height / 2),
            noFill, brandStrokeDesc, createWeightedStroke(Math.max(0.45, barThickness * 0.72)), noFill
          );
          if (connector) dimensionDefs.push(connector);
        }
      }

      const panelCurve = makeRoundedRectPolyCurve(
        panelX, panelY, m.width, m.height, m.height / 2
      );
      const panelDef = createFilledPanelDef(panelCurve, panelCol);
      if (!panelDef) throw new Error("Affinity could not create a measurement tag.");
      labelPanelDefs.push(panelDef);

      const captionBaseline = panelY + m.padY + m.captionSize;
      const valueBaseline = captionBaseline + m.captionSize * 1.05 + m.rowGap + effectiveFontSize * 1.08;
      const captionDef = createDimensionLabelDef(
        labelKind, { x: panelX + m.padX, y: captionBaseline }, m.captionSize, textCol, selectedFont
      );
      const valueDef = createDimensionLabelDef(
        labelText, { x: panelX + m.padX, y: valueBaseline }, effectiveFontSize, textCol, selectedFont
      );
      if (captionDef) textDefs.push(captionDef);
      if (valueDef) textDefs.push(valueDef);
    };
    const addDimensionBar = (x1, y1, x2, y2, isHoriz, spanDistance, labelSide, labelKind) => {
      const length = Math.hypot(x2 - x1, y2 - y1);
      if (length < 1) return;

      // A plain solid bar with square ends. No ticks, arrows, dots or caps
      // are drawn at the measurement endpoints. Build this node directly,
      // rather than appending cloned sub-curves to an aggregate PolyCurve.
      const barCurve = makeLinePolyCurve(x1, y1, x2, y2);
      const barDef = PolyCurveNodeDefinition.create(
        barCurve, noFill, brandStrokeDesc, lsdBar, noFill
      );
      if (!barDef) throw new Error("Affinity could not create a dimension-bar definition.");
      dimensionDefs.push(barDef);

      if (showText) {
        const labelText = formatValueString(spanDistance, unitIdx, precision, baseUnitPx, useComma);
        addDimensionLabel(labelText, x1, y1, x2, y2, isHoriz, labelSide, labelKind);
      }
    };

    const b = bounds;
    const topExtremePt = allVertices.reduce((best, p) => p.y < best.y ? p : best, { x: b.cx, y: b.y });
    const bottomExtremePt = allVertices.reduce((best, p) => p.y > best.y ? p : best, { x: b.cx, y: b.y + b.height });
    const leftExtremePt = allVertices.reduce((best, p) => p.x < best.x ? p : best, { x: b.x, y: b.cy });
    const rightExtremePt = allVertices.reduce((best, p) => p.x > best.x ? p : best, { x: b.x + b.width, y: b.cy });

    const addOverallWidth = (yLine, labelSide) => {
      addWitnessLine(leftExtremePt.x, leftExtremePt.y, b.x, yLine);
      addWitnessLine(rightExtremePt.x, rightExtremePt.y, b.x + b.width, yLine);
      addDimensionBar(b.x, yLine, b.x + b.width, yLine, true, b.width, labelSide, "OVERALL WIDTH");
    };

    const addOverallHeight = (xLine, labelSide) => {
      addWitnessLine(topExtremePt.x, topExtremePt.y, xLine, b.y);
      addWitnessLine(bottomExtremePt.x, bottomExtremePt.y, xLine, b.y + b.height);
      addDimensionBar(xLine, b.y, xLine, b.y + b.height, false, b.height, labelSide, "OVERALL HEIGHT");
    };

    const addFeatureSpan = (feature, span, lineOffset) => {
      const horizontal = feature.axis === "x";
      if (showText) {
        const label = formatValueString(span.length, unitIdx, precision, baseUnitPx, useComma);
        const tag = getTagMetrics(label, "FEATURE SPAN");
        const minReadable = feature.axis === "x" ? tag.width + 8 : tag.height + 8;
        if (span.length < minReadable) return false;
      }
      if (horizontal) {
        const yLine = feature.side === "top" ? b.y - lineOffset : b.y + b.height + lineOffset;
        addWitnessLine(span.a.x, span.a.y, span.a.x, yLine);
        addWitnessLine(span.b.x, span.b.y, span.b.x, yLine);
        addDimensionBar(span.a.x, yLine, span.b.x, yLine, true, span.length,
          feature.side === "top" ? "above" : "below", "FEATURE SPAN");
      } else {
        const xLine = feature.side === "left" ? b.x - lineOffset : b.x + b.width + lineOffset;
        addWitnessLine(span.a.x, span.a.y, xLine, span.a.y);
        addWitnessLine(span.b.x, span.b.y, xLine, span.b.y);
        addDimensionBar(xLine, span.a.y, xLine, span.b.y, false, span.length,
          feature.side === "left" ? "left" : "right", "FEATURE SPAN");
      }
      return true;
    };

    const bestFeature = findBestFeatureLandmarks(allVertices, b, detailLevel);

    if (dimMode === 0) {
      // Feature Spans: at most two useful intervals on one side of the mark.
      // The old implementation dimensioned both top and bottom, then added
      // overall widths and side heights, creating unnecessary visual clutter.
      let featureCount = 0;
      if (bestFeature && bestFeature.spans.length) {
        bestFeature.spans.forEach(span => {
          if (addFeatureSpan(bestFeature, span, offset)) featureCount++;
        });
      }
      if (!featureCount) {
        // A simple or circular silhouette may have no internal landmarks.
        // In that case show one reliable width reference rather than fabricate
        // feature measurements from arbitrary vertices.
        addOverallWidth(b.y - offset, "above");
      }
    } else if (dimMode === 1) {
      // Overall Bounds: the clean default, with one width and one height.
      addOverallWidth(b.y - offset, "above");
      addOverallHeight(b.x + b.width + offset, "right");
    } else if (dimMode === 2) {
      // Features + Totals: feature spans sit near the mark; total dimensions
      // occupy a second, more distant tier. Only one feature side is selected.
      if (bestFeature && bestFeature.spans.length) {
        bestFeature.spans.forEach(span => addFeatureSpan(bestFeature, span, offset));
      }
      addOverallWidth(b.y - offset - tierGap, "above");
      addOverallHeight(b.x + b.width + offset + tierGap, "right");
    } else if (dimMode === 3) {
      // Four-Sided Enclosure is intentionally explicit and therefore denser.
      const topY = b.y - offset;
      const bottomY = b.y + b.height + offset;
      const leftX = b.x - offset;
      const rightX = b.x + b.width + offset;

      addWitnessLine(leftExtremePt.x, leftExtremePt.y, b.x, topY);
      addWitnessLine(rightExtremePt.x, rightExtremePt.y, b.x + b.width, topY);
      addDimensionBar(b.x, topY, b.x + b.width, topY, true, b.width, "above", "OVERALL WIDTH");

      addWitnessLine(leftExtremePt.x, leftExtremePt.y, b.x, bottomY);
      addWitnessLine(rightExtremePt.x, rightExtremePt.y, b.x + b.width, bottomY);
      addDimensionBar(b.x, bottomY, b.x + b.width, bottomY, true, b.width, "below", "OVERALL WIDTH");

      addWitnessLine(topExtremePt.x, topExtremePt.y, leftX, b.y);
      addWitnessLine(bottomExtremePt.x, bottomExtremePt.y, leftX, b.y + b.height);
      addDimensionBar(leftX, b.y, leftX, b.y + b.height, false, b.height, "left", "OVERALL HEIGHT");

      addWitnessLine(topExtremePt.x, topExtremePt.y, rightX, b.y);
      addWitnessLine(bottomExtremePt.x, bottomExtremePt.y, rightX, b.y + b.height);
      addDimensionBar(rightX, b.y, rightX, b.y + b.height, false, b.height, "right", "OVERALL HEIGHT");
    } else if (dimMode === 4) {
      addOverallWidth(b.y - offset, "above");
    } else if (dimMode === 5) {
      addOverallHeight(b.x + b.width + offset, "right");
    }

    const subContainers = [];

    if (extensionDefs.length) {
      subContainers.push({ name: "01 — Construction Guides", defs: extensionDefs });
    }
    if (dimensionDefs.length) {
      subContainers.push({ name: "02 — Dimension Lines", defs: dimensionDefs });
    }
    if (labelPanelDefs.length) {
      subContainers.push({ name: "03 — Measurement Tags", defs: labelPanelDefs });
    }
    if (textDefs.length) {
      subContainers.push({ name: "04 — Measurement Typography", defs: textDefs });
    }

    return { subContainers };
  }

  function render(isPreview) {
    try {
      doc.executeCommand(DocumentCommand.createClearPreviews());
      const structure = buildCADStructure();
      if (!structure || !structure.subContainers.some(sc => sc.defs && sc.defs.length)) return false;
      const builder = AddChildNodesCommandBuilder.create();
      builder.setInsertionTargetSelection(Selection.create(doc, rawSel[0]));
      builder.setInsertionMode(InsertionMode.Top);
      structure.subContainers.forEach(sc => (sc.defs || []).forEach(def => builder.addNode(def)));
      doc.executeCommand(builder.createCommand(false, NodeChildType.Main), !!isPreview);
      return true;
    } catch (error) {
      try { doc.executeCommand(DocumentCommand.createClearPreviews()); } catch (e) {}
      console.log(
        "CAD Dimensioning preview error:",
        error && error.message ? error.message : error
      );
      return false;
    }
  }

  // Watch all controls for live preview
  [
    dimModeCombo, featureDetailCombo, unitCombo, xRatioTargetCombo, customXCtrl,
    decimalSeparatorCombo, precisionCtrl, offsetCtrl, tierGapCtrl, anchorGapCtrl,
    barThicknessCtrl, witnessWidthCtrl,
    showTextSwitch, fontPicker, fontSizeCtrl, textClearanceCtrl,
    brandColorPicker, guideColorPicker, labelPanelPicker, textColorPicker
  ].forEach(c => {
    try { c.setOnValueChangedHandler(() => render(true)); } catch (e) {}
  });

  render(true);

  const res = dlg.runModal();
  doc.executeCommand(DocumentCommand.createClearPreviews());

  if (isDialogOk(res)) {
    const structure = buildCADStructure();
    if (!structure || !structure.subContainers.some(sc => sc.defs && sc.defs.length)) {
      alert("No dimensions were generated. Adjust the options and try again.");
      return;
    }
    try {
      const rootBuilder = AddChildNodesCommandBuilder.create();
      rootBuilder.setInsertionTargetSelection(Selection.create(doc, rawSel[0]));
      rootBuilder.setInsertionMode(InsertionMode.Top);
      rootBuilder.addContainerNode(ContainerNodeDefinition.create("Logo Study — Measurements"));
      const rootCommand = rootBuilder.createCommand(false, NodeChildType.Main);
      doc.executeCommand(rootCommand);
      const root = toArray(rootCommand.newNodes)[0] || null;
      if (!root) throw new Error("Affinity did not confirm the root layer.");

      let expected = 0, actual = 0;
      for (const sc of structure.subContainers) {
        if (!sc.defs || !sc.defs.length) continue;
        const categoryBuilder = AddChildNodesCommandBuilder.create();
        categoryBuilder.setInsertionTarget(root);
        categoryBuilder.addContainerNode(ContainerNodeDefinition.create(sc.name));
        const categoryCommand = categoryBuilder.createCommand(false, NodeChildType.Main);
        doc.executeCommand(categoryCommand);
        const category = toArray(categoryCommand.newNodes)[0] || null;
        if (!category) throw new Error("Could not create category '" + sc.name + "'.");

        const defsBuilder = AddChildNodesCommandBuilder.create();
        defsBuilder.setInsertionTarget(category);
        sc.defs.forEach(def => defsBuilder.addNode(def));
        const defsCommand = defsBuilder.createCommand(false, NodeChildType.Main);
        doc.executeCommand(defsCommand);
        const createdCount = toArray(category.children).length;
        expected += sc.defs.length; actual += createdCount;
        if (createdCount !== sc.defs.length) throw new Error("Category '" + sc.name + "' contains " + createdCount + " of " + sc.defs.length + " expected elements.");
      }
      if (!expected || actual !== expected) throw new Error("Output did not confirm all elements.");
    } catch (error) {
      alert("Output is incomplete. The original geometry was not changed.\nDetails: " + String(error && error.message ? error.message : error) + "\nUse Undo to remove the partial output.");
    }
  }
}

main();