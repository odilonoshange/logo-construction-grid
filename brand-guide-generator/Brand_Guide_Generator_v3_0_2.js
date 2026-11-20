/**
 * name: Brand Guide Generator — Logo Proportions & Construction
 * version: 3.0.2 — Font Picker, Spacing & Resolution-Independent Stroke Controls
 * target: Affinity Designer / Affinity SDK 3.3.x
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
const {
  StoryDelta,
  ParagraphAlignXType,
  ParagraphLeadingType,
  ParagraphAttDoubleType
} = require("/storydelta.js");
const { GlyphAttDoubleType } = require("affinity:story");

const doc = Document.current;
const EPS = 1e-7;

// -----------------------------------------------------------------------------
// General helpers
// -----------------------------------------------------------------------------

function createWeightedStroke(weight) {
  const w = Math.max(0.01, Number(weight) || 0.1);
  return LineStyleDescriptor.createDefault(w);
}

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

// -----------------------------------------------------------------------------
// Exact Bézier bounds and geometric landmarks
// -----------------------------------------------------------------------------

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
        addUnique(bez.start);
        addUnique(bez.end);

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
  if (selected.length >= 3) for (let i = 0; i < selected.length - 1; i++) {
    const a = selected[i];
    const b = selected[i + 1];
    const length = Math.abs(b[axisKey] - a[axisKey]);
    if (length < minSpan || length > extent * 0.93) continue;
    spans.push({ a, b, length, index: i, prominence: Math.max(a.prominence || 0, b.prominence || 0) });
  }

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

// -----------------------------------------------------------------------------
// Vector line construction
// -----------------------------------------------------------------------------

function makeLinePolyCurve(x1, y1, x2, y2) {
  const cb = CurveBuilder.create();
  cb.beginXY(x1, y1);
  cb.lineToXY(x2, y2);
  const pc = PolyCurve.create();
  pc.addCurve(cb.createCurve());
  return pc;
}

/**
 * Pattern index: 0 = solid, 1 = dashed, 2 = dotted.
 * Patterns are made from ordinary open vector segments. This avoids relying
 * on version-dependent dash-array editing in LineStyleDescriptor. Weight is
 * already expressed in document pixels, so no DPI conversion is applied.
 */
function makePatternedLinePolyCurve(x1, y1, x2, y2, patternIndex, weightPx) {
  const pc = PolyCurve.create();
  const dx = x2 - x1;
  const dy = y2 - y1;
  const length = Math.hypot(dx, dy);
  if (length < 0.01) return pc;

  if (patternIndex === 0) {
    const cb = CurveBuilder.create();
    cb.beginXY(x1, y1);
    cb.lineToXY(x2, y2);
    pc.addCurve(cb.createCurve());
    return pc;
  }

  // Stroke controls are stored in document pixels. Do not convert again here.
  const strokePx = Math.max(0.2, Number(weightPx) || 0.25);
  let dashLength;
  let gapLength;

  if (patternIndex === 2) {
    // Small separated strokes read as fine dots at normal logo-study scale.
    dashLength = Math.max(1.0, strokePx * 1.45);
    gapLength = Math.max(3.2, strokePx * 4.0);
  } else {
    dashLength = Math.max(6.0, strokePx * 8.0);
    gapLength = Math.max(4.0, strokePx * 5.0);
  }

  const ux = dx / length;
  const uy = dy / length;
  let cursor = 0;
  let segmentCount = 0;
  const maxSegments = 1800;

  while (cursor < length && segmentCount < maxSegments) {
    const end = Math.min(cursor + dashLength, length);
    if (end - cursor > 0.15) {
      const cb = CurveBuilder.create();
      cb.beginXY(x1 + ux * cursor, y1 + uy * cursor);
      cb.lineToXY(x1 + ux * end, y1 + uy * end);
      pc.addCurve(cb.createCurve());
      segmentCount++;
    }
    cursor = end + gapLength;
  }
  return pc;
}

function formatValueString(valInPoints, unitIndex, precision, baseUnitPx, useComma) {
  let str = "";
  if (unitIndex === 0) {
    const xVal = valInPoints / Math.max(0.1, baseUnitPx);
    str = xVal.toFixed(precision);
    if (precision > 0) str = str.replace(/0+$/, "").replace(/\.$/, "");
    if (useComma) str = str.replace(".", ",");
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
  if (useComma) str = str.replace(".", ",");
  return str;
}

function createDimensionLabelDef(text, pos, textPt, colourObj, fontFamily, alignment) {
  try {
    const sb = StoryBuilder.create();
    sb.setToArtisticTextDefaultStyle(doc.dpi, doc.format);

    const align = alignment === undefined ? ParagraphAlignXType.Left : alignment;
    sb.applyParagraphDelta(StoryDelta.createAlignX(align));
    sb.applyParagraphDelta(StoryDelta.createLeadingType(ParagraphLeadingType.ExactlyAbsolute));
    sb.applyParagraphDelta(StoryDelta.createParagraphDouble(
      ParagraphAttDoubleType.AbsoluteLeading,
      Math.max(textPt * 1.35, textPt + 2)
    ));

    if (fontFamily) sb.applyGlyphDelta(StoryDelta.createFamilyName(fontFamily));
    sb.applyGlyphDelta(StoryDelta.createGlyphDouble(GlyphAttDoubleType.Height, textPt));
    sb.applyGlyphDelta(StoryDelta.createBrushFill(FillDescriptor.createSolid(colourObj)));
    sb.addText(text);

    const def = ArtTextNodeDefinition.createFromStoryBuilder({ x: pos.x, y: pos.y }, sb);
    if (def) {
      def.userDescription = "Brand guide label — " + text;
      return def;
    }
  } catch (e) {
    console.log("Brand guide text creation error:", e && e.message ? e.message : e);
  }
  return null;
}

function createStyledLineDefinition(x1, y1, x2, y2, colour, weight, pattern, noFill) {
  const curve = makePatternedLinePolyCurve(x1, y1, x2, y2, pattern, weight);
  if (!curve || curve.curveCount === 0) return null;
  return PolyCurveNodeDefinition.create(
    curve,
    noFill,
    FillDescriptor.createSolid(colour),
    createWeightedStroke(weight),
    noFill
  );
}

// -----------------------------------------------------------------------------
// Main
// -----------------------------------------------------------------------------

function main() {
  if (!doc || !doc.selection || doc.selection.length === 0) {
    alert("Select a logo or vector shape to generate a brand guide.");
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

  // Exact unified bounds from cubic Bézier extrema.
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
    x: minX,
    y: minY,
    width: maxX - minX,
    height: maxY - minY,
    cx: (minX + maxX) / 2,
    cy: (minY + maxY) / 2
  };
  const vertexTolerance = Math.max(EPS, Math.min(bounds.width, bounds.height) * 0.0005);
  const allVertices = extractAllGeometricVertices(polyCurves, vertexTolerance);

  // Follow the FontPicker workflow used by Visual.af:
  // initialise through .text and read .fontFamily.name with .text as fallback.
  const { Font, FontFamily } = require("/fonts.js");
  const installedFontFamilies = new Set([...FontFamily.all].map(f => f.name));
  const preferredFonts = ["Inter", "Helvetica Neue", "SF Pro Text", "Segoe UI"];
  const font0 = preferredFonts.find(name => installedFontFamilies.has(name)) || Font.createDefault().familyName;
  const pxPerPt = Math.max(0.1, Number(doc.dpi) || 72) / 72;

  // ---------------------------------------------------------------------------
  // Compact dialog layout. Retain the original 620 px footprint.
  // ---------------------------------------------------------------------------

  const dlg = Dialog.create("Brand Guide Generator — Logo Construction");
  dlg.initialWidth = 620;
  dlg.isResizable = true;

  const colLeft = dlg.addColumn();
  const colRight = dlg.addColumn();

  const setupGrp = colLeft.addGroup("Study Setup");
  const visualPresetCombo = setupGrp.addComboBox("Visual Style", ["Editorial", "Technical", "Minimal", "Geometric"], 0);
  attachTip(visualPresetCombo, "Applies a coordinated visual system. The line controls remain editable.");

  const dimModeCombo = setupGrp.addComboBox("Measurement Focus", [
    "Overall Dimensions",
    "Feature Dimensions",
    "Features + Overall Dimensions"
  ], 0);
  attachTip(dimModeCombo, "Choose overall dimensions, meaningful silhouette features, or both.");

  const featureDetailCombo = setupGrp.addComboBox("Feature Detail", [
    "Primary Landmarks",
    "Balanced Landmarks",
    "Detailed Landmarks"
  ], 1);
  attachTip(featureDetailCombo, "Controls how many meaningful silhouette features may be dimensioned.");

  const unitGrp = colLeft.addGroup("Proportions & Units");
  const unitCombo = unitGrp.addComboBox("Units", [
    "Proportional X Units",
    "Pixels (px)",
    "Millimeters (mm)",
    "Centimeters (cm)",
    "Inches (in)"
  ], 0);

  const xRatioTargetCombo = unitGrp.addComboBox("1X Definition", [
    "Total Width = 10x",
    "Total Width = 8x",
    "Total Width = 12x",
    "Total Height = 10x",
    "Custom X (px)"
  ], 0);
  const customXCtrl = unitGrp.addUnitValueEditor("Custom 1X (px)", UnitType.Pixel, UnitType.Pixel, bounds.width / 10, 1, 5000);
  customXCtrl.showPopupSlider = true;
  const precisionCtrl = unitGrp.addUnitValueEditor("Decimal Precision", UnitType.Number, UnitType.Number, 2, 0, 3);
  precisionCtrl.precision = 0;

  const spacingGrp = colLeft.addGroup("Dimension Placement");
  const offsetCtrl = spacingGrp.addUnitValueEditor("Primary Offset (px)", UnitType.Pixel, UnitType.Pixel, 38, 0, 2000);
  offsetCtrl.showPopupSlider = true;
  const tierGapCtrl = spacingGrp.addUnitValueEditor("Secondary Tier Gap (px)", UnitType.Pixel, UnitType.Pixel, 30, 0, 2000);
  tierGapCtrl.showPopupSlider = true;
  attachTip(tierGapCtrl, "Only separates feature measurements from overall dimensions in the combined measurement mode.");
  const anchorGapCtrl = spacingGrp.addUnitValueEditor("Anchor Clearance (px)", UnitType.Pixel, UnitType.Pixel, 6, 0, 500);
  anchorGapCtrl.showPopupSlider = true;
  attachTip(anchorGapCtrl, "Creates a visible gap between the logo silhouette and the start of each projection guide.");

  function addStrokeWeightEditor(group, label, initialPt) {
    // Store the stroke in pixels and display it in points, as in Affinity's
    // official Crop Marks scripting tutorial. No arbitrary maximum is set.
    const ctrl = group.addUnitValueEditor(
      label,
      UnitType.Pixel,
      UnitType.Point,
      initialPt * pxPerPt,
      0.01 * pxPerPt
    );
    try { ctrl.setHasNoMaxValue(true); } catch (e) {}
    try { ctrl.precision = 2; } catch (e) {}
    return ctrl;
  }

  const guideGrp = colRight.addGroup("Construction Guides");
  const showProjectionSwitch = guideGrp.addSwitch("Projection Guides", true);
  const guidePatternCombo = guideGrp.addComboBox("Guide Pattern", ["Continuous", "Dashed", "Dotted"], 0);
  const guideWeightCtrl = addStrokeWeightEditor(guideGrp, "Guide Weight (pt)", 0.25);
  const guideColorPicker = guideGrp.addColourPicker("Guide Colour", Colour.createRGBA8({ r: 145, g: 151, b: 160, alpha: 175 }));
  guideColorPicker.value = Colour.createRGBA8({ r: 145, g: 151, b: 160, alpha: 175 });

  const constructionCombo = guideGrp.addComboBox("Construction Reference", [
    "None",
    "Open Corner Frame",
    "Full Bounding Frame",
    "Centre Axes",
    "Diagonals",
    "Open Frame + Axes",
    "Full Frame + Axes",
    "Clear Space 0.5X",
    "Clear Space 1X",
    "Clear Space 2X",
    "Clear Space 1X + Axes"
  ], 0);
  attachTip(constructionCombo, "Adds one optional geometric reference around or through the logo. Clear-space values use the selected 1X unit.");

  const dimensionGrp = colRight.addGroup("Dimension Lines");
  const dimensionPatternCombo = dimensionGrp.addComboBox("Line Pattern", ["Continuous", "Dashed", "Dotted"], 0);
  const barThicknessCtrl = addStrokeWeightEditor(dimensionGrp, "Line Weight (pt)", 0.75);
  const dimensionColorPicker = dimensionGrp.addColourPicker("Dimension Colour", Colour.createRGBA8({ r: 54, g: 61, b: 70, alpha: 255 }));
  dimensionColorPicker.value = Colour.createRGBA8({ r: 54, g: 61, b: 70, alpha: 255 });

  const textGrp = colRight.addGroup("Typography & Labels");
  const showTextSwitch = textGrp.addSwitch("Show Labels", true);
  const fontPicker = textGrp.addFontPicker("Font");
  fontPicker.text = font0;
  attachTip(fontPicker, "Uses the selected font family in the live preview and final labels.");
  const fontSizeCtrl = textGrp.addUnitValueEditor(
    "Text Size (pt)",
    UnitType.Pixel,
    UnitType.Point,
    12 * pxPerPt,
    6 * pxPerPt,
    36 * pxPerPt
  );
  fontSizeCtrl.showPopupSlider = true;
  fontSizeCtrl.precision = 1;
  const labelStyleCombo = textGrp.addComboBox("Label Layout", ["Caption + Value", "Value Only"], 0);

  // ---------------------------------------------------------------------------
  // Coordinated starting styles. Users can edit every value afterwards.
  // ---------------------------------------------------------------------------

  const visualPresets = [
    {
      name: "Editorial",
      dimensionColor: { r: 54, g: 61, b: 70, alpha: 255 },
      guideColor: { r: 145, g: 151, b: 160, alpha: 175 },
      dimensionWeight: 0.75,
      guideWeight: 0.25,
      dimensionPattern: 0,
      guidePattern: 0,
      offset: 38,
      tierGap: 30,
      anchorGap: 6,
      fontSize: 12,
      labelStyle: 0,
      construction: 0
    },
    {
      name: "Technical",
      dimensionColor: { r: 35, g: 87, b: 112, alpha: 255 },
      guideColor: { r: 112, g: 157, b: 174, alpha: 190 },
      dimensionWeight: 0.72,
      guideWeight: 0.28,
      dimensionPattern: 0,
      guidePattern: 1,
      offset: 32,
      tierGap: 28,
      anchorGap: 6,
      fontSize: 10.5,
      labelStyle: 0,
      construction: 5
    },
    {
      name: "Minimal",
      dimensionColor: { r: 61, g: 66, b: 72, alpha: 255 },
      guideColor: { r: 174, g: 181, b: 187, alpha: 155 },
      dimensionWeight: 0.5,
      guideWeight: 0.18,
      dimensionPattern: 0,
      guidePattern: 0,
      offset: 30,
      tierGap: 24,
      anchorGap: 4,
      fontSize: 10,
      labelStyle: 1,
      construction: 0
    },
    {
      name: "Geometric",
      dimensionColor: { r: 151, g: 105, b: 47, alpha: 255 },
      guideColor: { r: 194, g: 164, b: 112, alpha: 185 },
      dimensionWeight: 0.85,
      guideWeight: 0.25,
      dimensionPattern: 0,
      guidePattern: 1,
      offset: 40,
      tierGap: 36,
      anchorGap: 8,
      fontSize: 11,
      labelStyle: 0,
      construction: 6
    }
  ];

  let applyingPreset = false;
  let activePresetIndex = visualPresetCombo.selectedIndex;

  function setControlValue(control, property, value) {
    try { control[property] = value; } catch (e) {}
  }

  function applyVisualPreset(index) {
    const p = visualPresets[index] || visualPresets[0];
    applyingPreset = true;
    activePresetIndex = index;

    setControlValue(dimensionColorPicker, "value", Colour.createRGBA8(p.dimensionColor));
    setControlValue(guideColorPicker, "value", Colour.createRGBA8(p.guideColor));
    setControlValue(barThicknessCtrl, "value", p.dimensionWeight * pxPerPt);
    setControlValue(guideWeightCtrl, "value", p.guideWeight * pxPerPt);
    setControlValue(dimensionPatternCombo, "selectedIndex", p.dimensionPattern);
    setControlValue(guidePatternCombo, "selectedIndex", p.guidePattern);
    setControlValue(offsetCtrl, "value", p.offset);
    setControlValue(tierGapCtrl, "value", p.tierGap);
    setControlValue(anchorGapCtrl, "value", p.anchorGap);
    setControlValue(fontSizeCtrl, "value", p.fontSize * pxPerPt);
    setControlValue(labelStyleCombo, "selectedIndex", p.labelStyle);
    setControlValue(constructionCombo, "selectedIndex", p.construction);

    applyingPreset = false;
    render(true);
  }

  // ---------------------------------------------------------------------------
  // Measurement settings
  // ---------------------------------------------------------------------------

  function getBaseUnitPixels() {
    const targetIdx = xRatioTargetCombo.selectedIndex;
    if (targetIdx === 0) return bounds.width / 10;
    if (targetIdx === 1) return bounds.width / 8;
    if (targetIdx === 2) return bounds.width / 12;
    if (targetIdx === 3) return bounds.height / 10;
    return customXCtrl.value;
  }

  function getSelectedFontFamily() {
    try {
      const family = fontPicker.fontFamily;
      if (family && typeof family.name === "string" && family.name.length) return family.name;
    } catch (e) {}
    try {
      const typedFamily = String(fontPicker.text || "").trim();
      if (typedFamily) return typedFamily;
    } catch (e) {}
    return font0;
  }

  function buildCADStructure() {
    const dimMode = dimModeCombo.selectedIndex;
    const detailLevel = featureDetailCombo.selectedIndex;
    const unitIdx = unitCombo.selectedIndex;
    const precision = Math.max(0, Math.floor(precisionCtrl.value));
    const useComma = true; // Portuguese decimal notation.
    const baseUnitPx = getBaseUnitPixels();

    const offset = offsetCtrl.value;
    const tierGap = tierGapCtrl.value;
    const anchorGap = anchorGapCtrl.value;

    const dimensionWeight = barThicknessCtrl.value;
    const guideWeight = guideWeightCtrl.value;
    const dimensionPattern = dimensionPatternCombo.selectedIndex;
    const guidePattern = guidePatternCombo.selectedIndex;

    const showText = showTextSwitch.value;
    const selectedFont = showText ? getSelectedFontFamily() : font0;
    const fontSize = fontSizeCtrl.value;
    const textGap = Math.max(10, fontSize * 0.42);
    const labelLayout = labelStyleCombo.selectedIndex;

    const dimensionCol = dimensionColorPicker.value || Colour.createRGBA8({ r: 54, g: 61, b: 70, alpha: 255 });
    const guideCol = guideColorPicker.value || Colour.createRGBA8({ r: 145, g: 151, b: 160, alpha: 175 });
    const textCol = dimensionCol;

    const noFill = FillDescriptor.createNone();
    const extensionDefs = [];
    const dimensionDefs = [];
    const textDefs = [];
    const witnessKeys = new Set();

    const addGuideSegment = (x1, y1, x2, y2) => {
      if (Math.hypot(x2 - x1, y2 - y1) < 1) return;
      const def = createStyledLineDefinition(x1, y1, x2, y2, guideCol, guideWeight, guidePattern, noFill);
      if (!def) throw new Error("Affinity could not create a construction-guide definition.");
      extensionDefs.push(def);
    };

    const addWitnessLine = (vx, vy, targetX, targetY) => {
      if (!showProjectionSwitch.value) return;
      const dx = targetX - vx;
      const dy = targetY - vy;
      const len = Math.hypot(dx, dy);
      if (len < 1) return;

      const ux = dx / len;
      const uy = dy / len;
      const clearance = Math.min(anchorGap, Math.max(0, len - 1));
      const startX = vx + ux * clearance;
      const startY = vy + uy * clearance;
      const endX = targetX;
      const endY = targetY;
      const key = [startX, startY, endX, endY].map(v => Math.round(v * 10) / 10).join(":");
      if (witnessKeys.has(key)) return;
      witnessKeys.add(key);
      addGuideSegment(startX, startY, endX, endY);
    };

    const addDimensionLabel = (labelText, x1, y1, x2, y2, isHoriz, labelSide, labelKind) => {
      if (!showText) return;

      const valueSize = Math.max(8, fontSize * 1.12);
      const captionSize = Math.max(7, fontSize * 0.68);
      const gap = Math.max(textGap, fontSize * 0.5);
      // The two text objects previously used only 1.12x the value size as
      // baseline separation. That is too tight for many font families.
      const stackDistance = valueSize + captionSize + Math.max(3, fontSize * 0.24);
      const centreX = (x1 + x2) / 2;
      const centreY = (y1 + y2) / 2;

      let valueX, valueY, captionX, captionY;
      let alignment;

      if (isHoriz) {
        alignment = ParagraphAlignXType.Centre;
        valueX = captionX = centreX;
        if (labelSide === "below") {
          captionY = y1 + gap + captionSize;
          valueY = captionY + stackDistance;
        } else {
          valueY = y1 - gap;
          captionY = valueY - stackDistance;
        }
      } else {
        alignment = labelSide === "left" ? ParagraphAlignXType.Right : ParagraphAlignXType.Left;
        valueX = captionX = labelSide === "left" ? x1 - gap : x1 + gap;
        valueY = centreY + valueSize * 0.42;
        captionY = valueY - stackDistance;
      }

      if (labelLayout === 1) {
        const valueDef = createDimensionLabelDef(
          labelText, { x: valueX, y: valueY }, valueSize, textCol, selectedFont, alignment
        );
        if (valueDef) textDefs.push(valueDef);
        return;
      }

      const captionDef = createDimensionLabelDef(
        labelKind, { x: captionX, y: captionY }, captionSize, dimensionCol, selectedFont, alignment
      );
      const valueDef = createDimensionLabelDef(
        labelText, { x: valueX, y: valueY }, valueSize, textCol, selectedFont, alignment
      );
      if (captionDef) textDefs.push(captionDef);
      if (valueDef) textDefs.push(valueDef);
    };
    const addDimensionBar = (x1, y1, x2, y2, isHoriz, spanDistance, labelSide, labelKind, includeLabel = true) => {
      const length = Math.hypot(x2 - x1, y2 - y1);
      if (length < 1) return;
      const def = createStyledLineDefinition(x1, y1, x2, y2, dimensionCol, dimensionWeight, dimensionPattern, noFill);
      if (!def) throw new Error("Affinity could not create a dimension-line definition.");
      dimensionDefs.push(def);

      if (showText && includeLabel) {
        const labelText = formatValueString(spanDistance, unitIdx, precision, baseUnitPx, useComma);
        addDimensionLabel(labelText, x1, y1, x2, y2, isHoriz, labelSide, labelKind);
      }
    };

    const b = bounds;
    const topExtremePt = allVertices.reduce((best, p) => p.y < best.y ? p : best, { x: b.cx, y: b.y });
    const bottomExtremePt = allVertices.reduce((best, p) => p.y > best.y ? p : best, { x: b.cx, y: b.y + b.height });
    const leftExtremePt = allVertices.reduce((best, p) => p.x < best.x ? p : best, { x: b.x, y: b.cy });
    const rightExtremePt = allVertices.reduce((best, p) => p.x > best.x ? p : best, { x: b.x + b.width, y: b.cy });

    const addOpenFrameCorner = (x, y, dirX, dirY, length) => {
      addGuideSegment(x, y, x + dirX * length, y);
      addGuideSegment(x, y, x, y + dirY * length);
    };

    const addConstructionReferences = () => {
      const mode = constructionCombo.selectedIndex;
      const cornerLength = Math.max(8, Math.min(b.width, b.height) * 0.07);
      const axisExtension = Math.max(offset * 0.55, Math.min(b.width, b.height) * 0.035, 10);

      const addOpenFrame = () => {
        addOpenFrameCorner(b.x, b.y, -1, -1, cornerLength);
        addOpenFrameCorner(b.x + b.width, b.y, 1, -1, cornerLength);
        addOpenFrameCorner(b.x, b.y + b.height, -1, 1, cornerLength);
        addOpenFrameCorner(b.x + b.width, b.y + b.height, 1, 1, cornerLength);
      };
      const addFullFrame = () => {
        addGuideSegment(b.x, b.y, b.x + b.width, b.y);
        addGuideSegment(b.x + b.width, b.y, b.x + b.width, b.y + b.height);
        addGuideSegment(b.x + b.width, b.y + b.height, b.x, b.y + b.height);
        addGuideSegment(b.x, b.y + b.height, b.x, b.y);
      };
      const addAxes = () => {
        addGuideSegment(b.x - axisExtension, b.cy, b.x + b.width + axisExtension, b.cy);
        addGuideSegment(b.cx, b.y - axisExtension, b.cx, b.y + b.height + axisExtension);
      };
      const addDiagonals = () => {
        addGuideSegment(b.x, b.y, b.x + b.width, b.y + b.height);
        addGuideSegment(b.x + b.width, b.y, b.x, b.y + b.height);
      };
      const addClearSpace = (scale) => {
        const margin = Math.max(0, baseUnitPx * scale);
        const x0 = b.x - margin;
        const y0 = b.y - margin;
        const x1 = b.x + b.width + margin;
        const y1 = b.y + b.height + margin;
        addGuideSegment(x0, y0, x1, y0);
        addGuideSegment(x1, y0, x1, y1);
        addGuideSegment(x1, y1, x0, y1);
        addGuideSegment(x0, y1, x0, y0);
        if (showText) {
          const clearLabelDef = createDimensionLabelDef(
            "CLEAR SPACE / " + scale + "X",
            { x: x0 + textGap, y: y0 - textGap },
            Math.max(7, fontSize * 0.70),
            textCol,
            selectedFont
          );
          if (clearLabelDef) textDefs.push(clearLabelDef);
        }
      };

      switch (mode) {
        case 1: addOpenFrame(); break;
        case 2: addFullFrame(); break;
        case 3: addAxes(); break;
        case 4: addDiagonals(); break;
        case 5: addOpenFrame(); addAxes(); break;
        case 6: addFullFrame(); addAxes(); break;
        case 7: addClearSpace(0.5); break;
        case 8: addClearSpace(1); break;
        case 9: addClearSpace(2); break;
        case 10: addClearSpace(1); addAxes(); break;
      }
    };

    const addOverallWidth = (yLine, labelSide, includeLabel = true) => {
      addWitnessLine(leftExtremePt.x, leftExtremePt.y, b.x, yLine);
      addWitnessLine(rightExtremePt.x, rightExtremePt.y, b.x + b.width, yLine);
      addDimensionBar(b.x, yLine, b.x + b.width, yLine, true, b.width, labelSide, "WIDTH", includeLabel);
    };

    const addOverallHeight = (xLine, labelSide, includeLabel = true) => {
      addWitnessLine(topExtremePt.x, topExtremePt.y, xLine, b.y);
      addWitnessLine(bottomExtremePt.x, bottomExtremePt.y, xLine, b.y + b.height);
      addDimensionBar(xLine, b.y, xLine, b.y + b.height, false, b.height, labelSide, "HEIGHT", includeLabel);
    };

    const addFeatureSpan = (feature, span, lineOffset) => {
      const horizontal = feature.axis === "x";
      if (showText) {
        const label = formatValueString(span.length, unitIdx, precision, baseUnitPx, useComma);
        const valueSize = Math.max(8, fontSize * 1.18);
        const captionSize = Math.max(7, fontSize * 0.70);
        const valueWidth = label.length * valueSize * 0.55;
        const labelWidth = labelLayout === 1
          ? valueWidth
          : Math.max(valueWidth, "FEATURE".length * captionSize * 0.54);
        const minReadable = horizontal ? labelWidth + 12 : captionSize * 1.2 + valueSize * 1.35 + 12;
        if (span.length < minReadable) return false;      }

      if (horizontal) {
        const yLine = feature.side === "top" ? b.y - lineOffset : b.y + b.height + lineOffset;
        addWitnessLine(span.a.x, span.a.y, span.a.x, yLine);
        addWitnessLine(span.b.x, span.b.y, span.b.x, yLine);
        addDimensionBar(span.a.x, yLine, span.b.x, yLine, true, span.length,
          feature.side === "top" ? "above" : "below", "FEATURE");
      } else {
        const xLine = feature.side === "left" ? b.x - lineOffset : b.x + b.width + lineOffset;
        addWitnessLine(span.a.x, span.a.y, xLine, span.a.y);
        addWitnessLine(span.b.x, span.b.y, xLine, span.b.y);
        addDimensionBar(xLine, span.a.y, xLine, span.b.y, false, span.length,
          feature.side === "left" ? "left" : "right", "FEATURE");
      }
      return true;
    };

    const bestFeature = findBestFeatureLandmarks(allVertices, b, detailLevel);

    // Construction references are independent of the measurement mode.
    addConstructionReferences();

    if (dimMode === 0) {
      // Overall dimensions: the clean default.
      addOverallWidth(b.y - offset, "above");
      addOverallHeight(b.x + b.width + offset, "right");
    } else if (dimMode === 1) {
      // Feature dimensions only. Simple silhouettes fall back to a reliable width.
      let featureCount = 0;
      if (bestFeature && bestFeature.spans.length) {
        bestFeature.spans.forEach(span => {
          if (addFeatureSpan(bestFeature, span, offset)) featureCount++;
        });
      }
      if (!featureCount) addOverallWidth(b.y - offset, "above");
    } else if (dimMode === 2) {
      // Features close to the mark, overall dimensions on a second tier.
      if (bestFeature && bestFeature.spans.length) {
        bestFeature.spans.forEach(span => addFeatureSpan(bestFeature, span, offset));
      }
      addOverallWidth(b.y - offset - tierGap, "above");
      addOverallHeight(b.x + b.width + offset + tierGap, "right");
    }

    const subContainers = [];
    if (extensionDefs.length) subContainers.push({ name: "01 — Construction Guides", defs: extensionDefs });
    if (dimensionDefs.length) subContainers.push({ name: "02 — Dimension Lines", defs: dimensionDefs });
    if (textDefs.length) subContainers.push({ name: "03 — Typography & Labels", defs: textDefs });

    return { subContainers };
  }

  // ---------------------------------------------------------------------------
  // Live preview
  // ---------------------------------------------------------------------------

  function hasOutput(structure) {
    return !!structure && structure.subContainers.some(sc => sc.defs && sc.defs.length);
  }

  function render(isPreview) {
    try {
      const structure = buildCADStructure();
      if (!hasOutput(structure)) {
        if (isPreview) doc.executeCommand(DocumentCommand.createClearPreviews());
        return false;
      }

      const builder = AddChildNodesCommandBuilder.create();
      builder.setInsertionTargetSelection(Selection.create(doc, rawSel[0]));
      builder.setInsertionMode(InsertionMode.Top);
      structure.subContainers.forEach(sc => (sc.defs || []).forEach(def => builder.addNode(def)));
      const command = builder.createCommand(false, NodeChildType.Main);

      // A new preview command replaces the previous preview automatically.
      // Do not clear it first: that causes unnecessary redraws and flicker.
      doc.executeCommand(command, !!isPreview);
      return true;
    } catch (error) {
      if (isPreview) {
        try { doc.executeCommand(DocumentCommand.createClearPreviews()); } catch (e) {}
      }
      console.log("Brand Guide Generator preview error:", error && error.message ? error.message : error);
      return false;
    }
  }

  function refreshControlAvailability() {
    // These controls are conditional by design, so users can see when their
    // setting is relevant instead of changing a value that cannot affect output.
    try { tierGapCtrl.isEnabled = dimModeCombo.selectedIndex === 2; } catch (e) {}
    try { anchorGapCtrl.isEnabled = !!showProjectionSwitch.value; } catch (e) {}
  }

  // This is the same dialog-wide change route used in Visual.af. It catches
  // FontPicker changes as well as numeric, colour, switch and combo controls.
  dlg.onControlValueChangedHandler = function () {
    if (applyingPreset) return;
    const nextPresetIndex = visualPresetCombo.selectedIndex;
    if (nextPresetIndex !== activePresetIndex) {
      applyVisualPreset(nextPresetIndex);
      refreshControlAvailability();
      return;
    }
    refreshControlAvailability();
    render(true);
  };

  refreshControlAvailability();

  render(true);

  const res = dlg.runModal();
  doc.executeCommand(DocumentCommand.createClearPreviews());

  if (!isDialogOk(res)) return;

  const structure = buildCADStructure();
  if (!hasOutput(structure)) {
    alert("No guide elements were generated. Adjust the options and try again.");
    return;
  }

  // ---------------------------------------------------------------------------
  // Commit output into an organised, editable layer structure
  // ---------------------------------------------------------------------------

  try {
    const rootBuilder = AddChildNodesCommandBuilder.create();
    rootBuilder.setInsertionTargetSelection(Selection.create(doc, rawSel[0]));
    rootBuilder.setInsertionMode(InsertionMode.Top);
    rootBuilder.addContainerNode(ContainerNodeDefinition.create("Brand Guide — Logo Construction"));
    const rootCommand = rootBuilder.createCommand(false, NodeChildType.Main);
    doc.executeCommand(rootCommand);
    const root = toArray(rootCommand.newNodes)[0] || null;
    if (!root) throw new Error("Affinity did not confirm the root layer.");

    let expected = 0;
    let actual = 0;
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
      expected += sc.defs.length;
      actual += createdCount;
      if (createdCount !== sc.defs.length) {
        throw new Error("Category '" + sc.name + "' contains " + createdCount + " of " + sc.defs.length + " expected elements.");
      }
    }

    if (!expected || actual !== expected) throw new Error("Output did not confirm all elements.");
  } catch (error) {
    alert(
      "Output is incomplete. The original logo geometry was not changed.\nDetails: " +
      String(error && error.message ? error.message : error) +
      "\nUse Undo to remove the partial output."
    );
  }
}

main();