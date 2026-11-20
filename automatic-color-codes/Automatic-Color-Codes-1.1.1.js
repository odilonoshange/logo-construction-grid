// Made by Visual.af
// v1.1.1: adds a configurable maximum number of extracted colours.
'use strict';

const LANG = 'en';

const { app } = require('/application.js');
const { Colour, ColourProfile, ColourProfileSet, ColourSpaceType } = require('/colours.js');
const { Dialog, DialogResult } = require('/dialog.js');
const { Document } = require('/document.js');
const { Curve, CurveBuilder, PolyCurve, Transform } = require('/geometry.js');
const { ArtTextNodeDefinition, ContainerNodeDefinition, PolyCurveNodeDefinition } = require('/nodes.js');
const { AddChildNodesCommandBuilder, CompoundCommandBuilder, DocumentCommand, InsertionMode, NodeChildType } = require('/commands.js');
const { FillDescriptor } = require('/fills.js');
const { FontWeight } = require('/fonts.js');
const { LineCap, LineJoin, LineStyle, LineStyleDescriptor, LineType } = require('/linestyle.js');
const { Selection } = require('/selections.js');
const { StoryBuilder } = require('/storybuilder.js');
const { StoryDelta, ParagraphAlignXType, ParagraphLeadingType, ParagraphAttDoubleType } = require('/storydelta.js');
const { GlyphAttDoubleType } = require('affinity:story');
const { PixelReaderRGBA8 } = require('/pixelaccessor');
const { UnitType } = require('/units.js');

const lin = (v) => {
  const c = v / 255;
  return c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4);
};

const luminance = (rgb) => 0.2126 * lin(rgb[0]) + 0.7152 * lin(rgb[1]) + 0.0722 * lin(rgb[2]);
const contrast = (l1, l2) => (Math.max(l1, l2) + 0.05) / (Math.min(l1, l2) + 0.05);

function lab(rgb) {
  const r = lin(rgb[0]), g = lin(rgb[1]), b = lin(rgb[2]);
  const x = 0.4360747 * r + 0.3850649 * g + 0.1430804 * b;
  const y = 0.2225045 * r + 0.7168786 * g + 0.0606169 * b;
  const z = 0.0139322 * r + 0.0971045 * g + 0.7141733 * b;
  const f = (t) => (t > 216 / 24389 ? Math.cbrt(t) : (24389 / 27 * t + 16) / 116);
  const fx = f(x / 0.96422), fy = f(y), fz = f(z / 0.82521);
  return [116 * fy - 16, 500 * (fx - fy), 200 * (fy - fz)];
}

function oklab(rgb) {
  const r = lin(rgb[0]), g = lin(rgb[1]), b = lin(rgb[2]);
  const l = Math.cbrt(0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b);
  const m = Math.cbrt(0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b);
  const s = Math.cbrt(0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b);
  return [
    0.2104542553 * l + 0.7936177850 * m - 0.0040720468 * s,
    1.9779984951 * l - 2.4285922050 * m + 0.4505937099 * s,
    0.0259040371 * l + 0.7827717662 * m - 0.8086757660 * s,
  ];
}
function oklch(rgb) {
  const [L, a, b] = oklab(rgb);
  const C = Math.hypot(a, b);
  let h = Math.atan2(b, a) * 180 / Math.PI;
  if (h < 0) h += 360;
  return [L, C, C < 1e-4 ? 0 : h];
}

function hueOf(r, g, b, max, d) {
  if (d === 0) return 0;
  const h = max === r ? (g - b) / d + (g < b ? 6 : 0) : max === g ? (b - r) / d + 2 : (r - g) / d + 4;
  return h * 60;
}
function hsl(rgb) {
  const r = rgb[0] / 255, g = rgb[1] / 255, b = rgb[2] / 255;
  const max = Math.max(r, g, b), min = Math.min(r, g, b), d = max - min, l = (max + min) / 2;
  const s = d === 0 ? 0 : d / (1 - Math.abs(2 * l - 1));
  return [hueOf(r, g, b, max, d), s * 100, l * 100];
}
function hsb(rgb) {
  const r = rgb[0] / 255, g = rgb[1] / 255, b = rgb[2] / 255;
  const max = Math.max(r, g, b), min = Math.min(r, g, b), d = max - min;
  return [hueOf(r, g, b, max, d), max === 0 ? 0 : d / max * 100, max * 100];
}

function editorialCMYK(cmyk, rgb, step, limit, grayK) {
  const snap = (v) => (v < step ? 0 : Math.min(100, Math.round(v / step) * step));
  if (grayK && Math.max(rgb[0], rgb[1], rgb[2]) - Math.min(rgb[0], rgb[1], rgb[2]) <= 3) {
    return [0, 0, 0, snap(100 - (rgb[0] + rgb[1] + rgb[2]) / 7.65)];
  }
  let [c, m, y, k] = cmyk.map(snap);
  if (c + m + y + k > limit && c + m + y > 0) {
    const f = Math.max(0, limit - k) / (c + m + y);
    [c, m, y] = [c, m, y].map((v) => Math.floor(v * f / step) * step);
  }
  return [c, m, y, k];
}

const INK_DARK = [17, 17, 17], INK_LIGHT = [255, 255, 255];
const inkOn = (rgb) => {
  const l = luminance(rgb);
  return contrast(l, luminance(INK_DARK)) >= contrast(l, 1) ? INK_DARK : INK_LIGHT;
};

function tintColour(rec, t) {
  if (rec.native) {
    const [c, m, y, k] = rec.cmykN;
    return Colour.createCMYKAf({ c: c * t / 100, m: m * t / 100, y: y * t / 100, k: k * t / 100, alpha: 1 });
  }
  const v = rec.rgb.map((x) => Math.round(255 - (255 - x) * t));
  return Colour.createRGBA8({ r: v[0], g: v[1], b: v[2], alpha: 255 });
}
const tintRGB = (rgb, t) => rgb.map((x) => Math.round(255 - (255 - x) * t));

function nativeTester() {
  const list = ColourProfile.getProfilesForColourSpace(ColourSpaceType.CMYK);
  const sets = list.slice(0, 2).map((p) => {
    const s = ColourProfileSet.create();
    s.setProfileForColourSpaceType(ColourSpaceType.CMYK, p);
    return s;
  });
  return (col) => {
    if (sets.length < 2) return false;
    const a = col.getCMYKAf(false, sets[0]), b = col.getCMYKAf(false, sets[1]);
    return Math.abs(a.c - b.c) + Math.abs(a.m - b.m) + Math.abs(a.y - b.y) + Math.abs(a.k - b.k) < 1e-4;
  };
}

const asColour = (c) => (c && c.rgba8 ? c : new Colour(c));

function isRasterImageNode(node) {
  if (!node) return false;
  try {
    if (node.isRasterNode || node.isImageNode) return true;
  } catch (e) { }
  try {
    const tag = String(node[Symbol.toStringTag] || '').toLowerCase();
    return tag.includes('raster') || tag.includes('image');
  } catch (e) { }
  return false;
}

function medianCutRasterColours(histogram, limit) {
  if (!histogram.length) return [];
  const boxes = [histogram.slice()];
  const weightOf = (box) => box.reduce((sum, item) => sum + item.count, 0);

  while (boxes.length < limit) {
    let bestIndex = -1, bestChannel = 0, bestScore = -1;
    for (let i = 0; i < boxes.length; i++) {
      const box = boxes[i];
      if (box.length < 2) continue;
      const min = [255, 255, 255], max = [0, 0, 0];
      for (const item of box) {
        const values = [item.r, item.g, item.b];
        for (let c = 0; c < 3; c++) {
          if (values[c] < min[c]) min[c] = values[c];
          if (values[c] > max[c]) max[c] = values[c];
        }
      }
      let channel = 0;
      if (max[1] - min[1] > max[channel] - min[channel]) channel = 1;
      if (max[2] - min[2] > max[channel] - min[channel]) channel = 2;
      const range = max[channel] - min[channel];
      const score = range * Math.log2(weightOf(box) + 1);
      if (score > bestScore) {
        bestScore = score;
        bestIndex = i;
        bestChannel = channel;
      }
    }
    if (bestIndex < 0) break;

    const box = boxes[bestIndex].slice().sort((a, b) => a[['r', 'g', 'b'][bestChannel]] - b[['r', 'g', 'b'][bestChannel]]);
    const half = weightOf(box) / 2;
    let accumulated = 0, splitAt = 1;
    for (let i = 0; i < box.length - 1; i++) {
      accumulated += box[i].count;
      splitAt = i + 1;
      if (accumulated >= half) break;
    }
    splitAt = Math.max(1, Math.min(box.length - 1, splitAt));
    boxes.splice(bestIndex, 1, box.slice(0, splitAt), box.slice(splitAt));
  }

  return boxes.map((box) => {
    let total = 0, r = 0, g = 0, b = 0, alpha = 0;
    for (const item of box) {
      total += item.count;
      r += item.r * item.count;
      g += item.g * item.count;
      b += item.b * item.count;
      alpha += item.alpha * item.count;
    }
    return {
      r: Math.round(r / total),
      g: Math.round(g / total),
      b: Math.round(b / total),
      alpha: Math.round(alpha / total),
      count: total,
    };
  });
}

function readRasterColours(node, top, quality, maxColours) {
  let raster = null, bitmap = null, reader = null;
  try {
    raster = node.rasterInterface;
    if (!raster || typeof raster.createCompatibleBitmap !== 'function') return [];

    bitmap = raster.createCompatibleBitmap(true);
    if (!bitmap) return [];
    const width = Math.floor(Number(bitmap.width));
    const height = Math.floor(Number(bitmap.height));
    if (!(width > 0 && height > 0)) return [];

    reader = PixelReaderRGBA8.create(bitmap);
    const perSide = Math.max(8, Math.min(128, Math.round(Number(quality) || 48)));
    const columns = Math.min(width, perSide);
    const rows = Math.min(height, perSide);
    const histogram = new Map();

    for (let gy = 0; gy < rows; gy++) {
      const y = Math.min(height - 1, Math.floor((gy + 0.5) * height / rows));
      for (let gx = 0; gx < columns; gx++) {
        const x = Math.min(width - 1, Math.floor((gx + 0.5) * width / columns));
        const px = reader.readPixel(x, y);
        if (!px || px.alpha <= 8) continue;

        const r = Math.max(0, Math.min(255, Math.round(px.r)));
        const g = Math.max(0, Math.min(255, Math.round(px.g)));
        const b = Math.max(0, Math.min(255, Math.round(px.b)));
        const alpha = Math.max(0, Math.min(255, Math.round(px.alpha)));
        const key = `${r},${g},${b},${alpha}`;
        const hit = histogram.get(key);
        if (hit) hit.count++;
        else histogram.set(key, { r, g, b, alpha, count: 1 });
      }
    }

    if (!histogram.size) return [];
    const box = (() => { try { return node.spreadBaseBox; } catch (e) { return null; } })();
    const src = {
      top,
      name: node.userDescription || '',
      x: box ? box.x + box.width / 2 : 0,
      y: box ? box.y + box.height / 2 : 0,
      h: box ? box.height : 0,
    };

    return medianCutRasterColours([...histogram.values()], normalizeMaxColours(maxColours)).map((sample) => ({
      colour: rgba([sample.r, sample.g, sample.b, sample.alpha]),
      kind: 'raster',
      sampleCount: sample.count,
      ...src,
    }));
  } catch (e) {
    return [];
  } finally {
    try { if (reader && typeof reader.dispose === 'function') reader.dispose(); } catch (e) { }
    try { if (bitmap && typeof bitmap.dispose === 'function') bitmap.dispose(); } catch (e) { }
  }
}

function collectColours(nodes, skip, p) {
  const found = [], texts = [];
  const add = (fill, kind, src) => {
    if (!fill) return;
    if (fill.colour) found.push({ colour: fill.colour, kind, ...src });
    else if (fill.gradient && p.gradients) {
      const g = fill.gradient;
      for (let i = 0; i < g.stopCount; i++) found.push({ colour: asColour(g.getStop(i).colour), kind: 'gradient', ...src });
    }
  };
  const walk = (n, top) => {
    if (n.isVisible === false) return;
    if (n.isContainerNode && n.description === skip) return;
    if (n.isTextNode) { texts.push({ node: n, top }); return; }
    if (p.images && isRasterImageNode(n)) found.push(...readRasterColours(n, top, p.imageQuality, p.maxColours));
    if ((n.isPolyCurveNode || n.isShapeNode) && n.isArtboardEnabled !== true) {
      let box = null;
      try { box = n.spreadBaseBox; } catch (e) { box = null; }
      const src = { top, name: n.userDescription || '', x: box ? box.x + box.width / 2 : 0, y: box ? box.y + box.height / 2 : 0, h: box ? box.height : 0 };
      try {
        for (const fd of n.brushFillInterface.allDescriptors) add(fd.fill, 'fill', src);
      } catch (e) { }
      if (p.strokes) {
        try {
          const li = n.lineStyleInterface;
          const fills = li.getAllFillDescriptors(), styles = li.getAllLineStyleDescriptors();
          fills.forEach((fd, i) => {
            const ls = (styles[i] || styles[0]).lineStyle;
            if (ls && ls.weight > 0 && ls.type !== LineType.None) add(fd.fill, 'stroke', src);
          });
        } catch (e) { }
      }
    }
    for (const ch of n.children) walk(ch, top);
  };
  nodes.forEach((n, i) => walk(n, i));
  return { found, texts };
}

function textColours(doc, t, skip, p) {
  doc.executeCommand(DocumentCommand.createConvertToCurves(Selection.create(doc, [t.node])));
  try {
    const r = collectColours([...doc.selection.nodes], skip, p).found;
    const name = t.node.userDescription || '';
    for (const f of r) { f.top = t.top; f.name = name; }
    return r;
  } finally {
    doc.executeCommand(DocumentCommand.createUndo());
  }
}

function uniqueColours(found, isNative) {
  const map = new Map(), out = [];
  for (const f of found) {
    const native = isNative(f.colour);
    let key, cmykN = null;
    if (native) {
      const c = f.colour.cmykaf;
      cmykN = [c.c * 100, c.m * 100, c.y * 100, c.k * 100];
      key = 'k' + cmykN.map((v) => Math.round(v * 10)).join(',') + ':' + Math.round(c.alpha * 255);
    } else {
      const c = f.colour.rgba8;
      key = `r${c.r},${c.g},${c.b},${c.alpha}`;
    }
    let rec = map.get(key);
    if (!rec) {
      rec = { colour: f.colour, native, cmykN, srcs: [], count: 0, index: out.length };
      map.set(key, rec);
      out.push(rec);
    }
    rec.srcs.push(f);
    const weight = Number(f.sampleCount);
    rec.count += Number.isFinite(weight) && weight > 0 ? weight : 1;
  }
  return out;
}

function derive(rec, set) {
  const c = rec.colour.getRGBA8(false, set);
  rec.rgb = [c.r, c.g, c.b];
  rec.alpha = c.alpha / 255;
  if (rec.native) rec.cmyk = rec.cmykN.slice();
  else {
    const k = rec.colour.getCMYKAf(false, set);
    rec.cmyk = [k.c * 100, k.m * 100, k.y * 100, k.k * 100];
  }
  rec.ok = oklab(rec.rgb);
  rec.lch = oklch(rec.rgb);
  rec.lum = luminance(rec.rgb);
}

function mergeSimilar(recs, tol) {
  if (tol <= 0) return recs;
  const sorted = recs.slice().sort((a, b) => b.count - a.count || a.index - b.index);
  const out = [];
  for (const r of sorted) {
    const hit = out.find((o) => Math.hypot(o.ok[0] - r.ok[0], o.ok[1] - r.ok[1], o.ok[2] - r.ok[2]) < tol);
    if (hit) { hit.srcs = hit.srcs.concat(r.srcs); hit.count += r.count; hit.index = Math.min(hit.index, r.index); hit.merged++; }
    else out.push(Object.assign(r, { merged: 0 }));
  }
  return out.sort((a, b) => a.index - b.index);
}

function readingOrder(recs) {
  const first = (r) => r.srcs[0];
  const s = recs.slice().sort((a, b) => first(a).y - first(b).y);
  const rows = [];
  for (const r of s) {
    const f = first(r), row = rows[rows.length - 1];
    if (row && Math.abs(f.y - row.y) <= Math.max(row.h, f.h, 1e-6) * 0.5) row.items.push(r);
    else rows.push({ y: f.y, h: f.h, items: [r] });
  }
  return rows.flatMap((row) => row.items.sort((a, b) => first(a).x - first(b).x || a.index - b.index));
}

function orderColours(recs, mode) {
  if (mode === 1) {
    const grey = (r) => r.lch[1] < 0.02;
    return recs.slice().sort((a, b) => (grey(a) - grey(b)) || (grey(a) ? a.lch[0] - b.lch[0] : a.lch[2] - b.lch[2] || a.lch[0] - b.lch[0]));
  }
  if (mode === 2) return recs.slice().sort((a, b) => a.lch[0] - b.lch[0]);
  if (mode === 3) return recs.slice().sort((a, b) => b.lch[0] - a.lch[0]);
  if (mode === 4) return recs.slice().sort((a, b) => b.count - a.count || a.index - b.index);
  return readingOrder(recs);
}

const hex2 = (v) => v.toString(16).toUpperCase().padStart(2, '0');
const r0 = (v) => String(Math.round(v) + 0);
const r1 = (v) => (Math.round(v * 10) / 10).toFixed(1);

function codeLines(rec, p, T) {
  const L = T.labels, out = [];
  if (p.hex) {
    let v = '#' + rec.rgb.map(hex2).join('');
    if (rec.alpha < 0.999) v += '  ' + r0(rec.alpha * 100) + '%';
    out.push([L.hex, v]);
  }
  if (p.rgb) out.push([L.rgb, rec.rgb.join(' ')]);
  if (p.cmyk) out.push([L.cmyk, rec.cmyk.map(r0).join(' ')]);
  if (p.cmykEd) {
    const ed = editorialCMYK(rec.cmyk, rec.rgb, STEPS[p.step], p.inkLimit, p.grayK && !rec.native);
    out.push([p.cmyk ? L.cmykEd : L.cmyk, ed.join(' ')]);
  }
  if (p.hsl) { const h = hsl(rec.rgb); out.push([L.hsl, `${r0(h[0]) % 360}° ${r0(h[1])}% ${r0(h[2])}%`]); }
  if (p.hsb) { const h = hsb(rec.rgb); out.push([L.hsb, `${r0(h[0]) % 360}° ${r0(h[1])}% ${r0(h[2])}%`]); }
  if (p.lab) out.push([L.lab, lab(rec.rgb).map(r0).join(' ')]);
  if (p.oklch) out.push([L.oklch, `${r1(rec.lch[0] * 100)}% ${(Math.round(rec.lch[1] * 1000) / 1000).toFixed(3)} ${r1(rec.lch[2])}`]);
  if (p.contrast) {
    const grade = (c) => (c >= 7 ? ' AAA' : c >= 4.5 ? ' AA' : c >= 3 ? ' ' + T.large : '');
    const w = contrast(rec.lum, 1), k = contrast(rec.lum, 0);
    out.push([L.onWhite, `${r1(w)}:1${grade(w)}`]);
    out.push([L.onBlack, `${r1(k)}:1${grade(k)}`]);
  }
  return out;
}

function textDef(doc, font, spec, x, y) {
  const sb = StoryBuilder.create();
  sb.setToArtisticTextDefaultStyle(doc.dpi, doc.rasterFormat);
  sb.applyParagraphDelta(StoryDelta.createAlignX(spec.align ? ParagraphAlignXType.Centre : ParagraphAlignXType.Left));
  sb.applyParagraphDelta(StoryDelta.createLeadingType(ParagraphLeadingType.ExactlyAbsolute));
  sb.applyParagraphDelta(StoryDelta.createParagraphDouble(ParagraphAttDoubleType.AbsoluteLeading, spec.lead));
  sb.applyGlyphDelta(StoryDelta.createFamilyName(font));
  spec.lines.forEach((runs, i) => {
    if (i) sb.addParagraphBreak();
    for (const r of runs) {
      sb.applyGlyphDelta(StoryDelta.createWeight(r.w));
      sb.applyGlyphDelta(StoryDelta.createGlyphDouble(GlyphAttDoubleType.Height, r.s));
      sb.applyGlyphDelta(StoryDelta.createGlyphDouble(GlyphAttDoubleType.CharacterSpacing, r.tr || 0));
      sb.applyGlyphDelta(StoryDelta.createBrushFill(FillDescriptor.createSolid(rgba(r.c))));
      sb.addText(r.t);
    }
  });
  return ArtTextNodeDefinition.createFromStoryBuilder({ x, y }, sb);
}

const REF = 100;
const measureKey = (font, w, tr, text) => `${font}|${w}|${tr}|${text}`;

const rgba = (c) => Colour.createRGBA8({ r: c[0], g: c[1], b: c[2], alpha: c.length > 3 ? c[3] : 255 });

function roundRect(x, y, w, h, radii) {
  const lim = Math.min(w, h) / 2;
  const [tl, tr, br, bl] = radii.map((v) => Math.max(0, Math.min(v, lim)));
  if (tl + tr + br + bl < 1e-6) return Curve.createRectangle({ x, y, width: w, height: h });
  const k = 0.5522847498;
  const b = CurveBuilder.create().beginXY(x + tl, y);
  if (w - tl - tr > 1e-6) b.lineToXY(x + w - tr, y);
  if (tr) b.addBezierXY(x + w - tr * (1 - k), y, x + w, y + tr * (1 - k), x + w, y + tr);
  if (h - tr - br > 1e-6) b.lineToXY(x + w, y + h - br);
  if (br) b.addBezierXY(x + w, y + h - br * (1 - k), x + w - br * (1 - k), y + h, x + w - br, y + h);
  if (w - br - bl > 1e-6) b.lineToXY(x + bl, y + h);
  if (bl) b.addBezierXY(x + bl * (1 - k), y + h, x, y + h - bl * (1 - k), x, y + h - bl);
  if (h - bl - tl > 1e-6) b.lineToXY(x, y + tl);
  if (tl) b.addBezierXY(x, y + tl * (1 - k), x + tl * (1 - k), y, x + tl, y);
  return b.close().createCurve();
}

function blockSpec(lines, M, look) {
  const lab = { w: FontWeight.Normal, s: M.fsL, c: look.text.concat(150) };
  const val = { w: FontWeight.Medium, s: M.fsC, c: look.text.concat(255) };
  return {
    labels: { align: 0, lead: M.lead, lines: lines.map((l) => [Object.assign({ t: l[0] }, lab)]) },
    values: { align: 0, lead: M.lead, lines: lines.map((l) => [Object.assign({ t: l[1] }, val)]) },
  };
}

function textMetrics(W, p) {
  const k = p.textSize / 100;
  const fsC = W * 0.066 * k;
  return {
    fsT: W * 0.086 * k, fsC, fsL: fsC * 0.84, fsTint: fsC * 0.8,
    lead: fsC * 1.5, gapTitle: W * 0.075 * k,
  };
}

const NAME = 'Automatic Color Codes';
const VERSION = '1.1.1';
const GROUP = 'Automatic Color Codes';
const STEPS = [1, 5, 10];
const MAX_COLOURS = 64;
const normalizeMaxColours = (value) => Math.max(1, Math.min(MAX_COLOURS, Math.round(Number(value) || MAX_COLOURS)));
const TINTS = [0.8, 0.6, 0.4, 0.2];

const STYLES = [
  { params: { card: '#FFFFFF', text: '#111111', border: '#E3E3E3' } },
  { params: { card: '#161616', text: '#F4F4F4', border: '#00000000' } },
  { params: { card: '#F2EEE6', text: '#201C17', border: '#00000000' } },
  { params: { card: '#00000000', text: '#111111', border: '#111111' } },
  { params: { card: '#00000000', text: '#111111', border: '#00000000' } },
];

const LAYOUTS = [
  { key: 'cards', spacing: 12, radius: 5 },
  { key: 'columns', spacing: 0, radius: 0 },
  { key: 'circles', spacing: 16, radius: 6 },
  { key: 'list', spacing: 10, radius: 10 },
  { key: 'tags', spacing: 10, radius: 8 },
];

const DEFAULTS = {
  strokes: true, gradients: false, images: true, maxColours: 64, imageQuality: 48, merge: 0, order: 0, title: 0,
  position: 0, perRow: 0, spacing: 12, radius: 5,
  hex: true, rgb: true, cmyk: false, cmykEd: true, hsl: false, hsb: false, lab: false, oklch: false, contrast: false, tints: false,
  step: 1, inkLimit: 300, grayK: true,
  textSize: 100,
};

const CONTROLS = [
  { key: 'strokes',      kind: 'switch', group: 'gSource', column: 0 },
  { key: 'gradients',    kind: 'switch', group: 'gSource', column: 0 },
  { key: 'images',       kind: 'switch', group: 'gSource', column: 0 },
  { key: 'maxColours',   kind: 'range',  group: 'gSource', column: 0, min: 1, max: 64, decimals: 0 },
  { key: 'imageQuality', kind: 'range',  group: 'gSource', column: 0, min: 16, max: 96, decimals: 0, on: 'images' },
  { key: 'merge',        kind: 'range',  group: 'gSource', column: 0, min: 0, max: 20, decimals: 0 },
  { key: 'order',     kind: 'select', group: 'gSource', column: 0 },
  { key: 'title',     kind: 'select', group: 'gSource', column: 0 },
  { key: 'position',  kind: 'select', group: 'gLayout', column: 0 },
  { key: 'perRow',    kind: 'range',  group: 'gLayout', column: 0, min: 0, max: 24, decimals: 0 },
  { key: 'spacing',   kind: 'range',  group: 'gLayout', column: 0, min: 0, max: 100, decimals: 0, unit: '%' },
  { key: 'radius',    kind: 'range',  group: 'gLayout', column: 0, min: 0, max: 50, decimals: 0, unit: '%' },
  { key: 'hex',       kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'rgb',       kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'cmyk',      kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'cmykEd',    kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'hsl',       kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'hsb',       kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'lab',       kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'oklch',     kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'contrast',  kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'tints',     kind: 'switch', group: 'gCodes', column: 1 },
  { key: 'profile',   kind: 'profile', group: 'gCmyk', column: 2 },
  { key: 'step',      kind: 'select', group: 'gCmyk', column: 2, on: 'cmykEd' },
  { key: 'inkLimit',  kind: 'range',  group: 'gCmyk', column: 2, on: 'cmykEd', min: 200, max: 400, decimals: 0, unit: '%' },
  { key: 'grayK',     kind: 'switch', group: 'gCmyk', column: 2, on: 'cmykEd' },
  { key: 'font',      kind: 'font',   group: 'gText', column: 2 },
  { key: 'textSize',  kind: 'range',  group: 'gText', column: 2, min: 40, max: 250, decimals: 0, unit: '%' },
  { key: 'card',      kind: 'colour', group: 'gText', column: 2, look: true, none: true },
  { key: 'text',      kind: 'colour', group: 'gText', column: 2, look: true },
  { key: 'border',    kind: 'colour', group: 'gText', column: 2, look: true, none: true },
];

const STRINGS = {
  es: {
    noDoc: 'Abre un documento y selecciona los objetos con los colores que quieres documentar.',
    noSel: 'Primero selecciona los objetos con los colores que quieres documentar. Pueden ser formas, curvas, textos o grupos.',
    noColours: 'La selección no tiene rellenos ni trazos de color sólido. Selecciona formas, curvas o textos con color y vuelve a ejecutar el script.',
    layout: 'Disposición', layoutOptions: ['Fichas', 'Columnas', 'Círculos', 'Lista', 'Etiquetas'],
    style: 'Estilo', styleOptions: ['Claro', 'Oscuro', 'Papel', 'Contorno', 'Mínimo'], size: 'Tamaño',
    sizeHint: 'Ancho de cada muestra. Todo lo demás (textos, márgenes, separación) se mide en proporción.',
    gSource: 'Colores',
    maxColours: 'Máximo de colores', maxColoursHint: 'Define el número máximo de colores de la paleta. Si la selección tiene menos colores distintos, solo se usarán los disponibles. Límite: 64.', gLayout: 'Distribución', gCodes: 'Códigos', gCmyk: 'CMYK', gText: 'Texto y fondo',
    strokes: 'Incluir trazos', strokesHint: 'Suma el color de los trazos además del de los rellenos.',
    gradients: 'Incluir degradados', gradientsHint: 'Suma cada parada de los degradados como un color.',
    merge: 'Unir parecidos', mergeHint: 'Junta los colores que casi no se distinguen. Con 0 solo se unen los idénticos; súbelo para una ilustración con muchos tonos.',
    order: 'Orden', orderOptions: ['Como en el lienzo', 'Por tono', 'De oscuro a claro', 'De claro a oscuro', 'Los más usados primero'],
    title: 'Título', titleOptions: ['Nombre de la capa', 'Número', 'Sin título'],
    titleHint: 'Con «Nombre de la capa», el color de un objeto que renombraste en el panel Capas lleva ese nombre; los demás, un número.',
    position: 'Posición', positionOptions: ['Debajo', 'A la derecha', 'Encima', 'A la izquierda'],
    perRow: 'Por fila', perRowHint: 'Cuántos colores van en cada fila. Con 0 se calcula solo.',
    spacing: 'Separación', spacingHint: 'Espacio entre muestras, en porcentaje del tamaño.',
    radius: 'Esquinas', radiusHint: 'Redondeo de las esquinas, en porcentaje del tamaño.',
    hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykHint: 'CMYK convertido con el perfil elegido, sin redondear. Un color que ya es CMYK se muestra tal cual.',
    cmykEd: 'CMYK editorial', cmykEdHint: 'CMYK listo para imprenta: valores en múltiplos de 5, sin tintas por debajo de ese paso y con la suma de las cuatro dentro del límite de tinta.',
    hsl: 'HSL', hsb: 'HSB', hsbHint: 'Tono, saturación y brillo, como en el selector de color de Photoshop y Figma.',
    lab: 'LAB', labHint: 'L*a*b* con blanco D50, como en el panel Color de Affinity.',
    oklch: 'OKLCH', oklchHint: 'Luminosidad, croma y tono en OKLCH, el formato de color de CSS moderno.',
    contrast: 'Contraste WCAG', contrastHint: 'Contraste contra blanco y contra negro, con el nivel que cumple: AAA, AA o AA solo para texto grande.',
    tints: 'Tintes', tintsHint: 'Agrega los tintes al 80, 60, 40 y 20 % de cada color. En un color CMYK bajan las tintas, como en la imprenta.',
    profile: 'Perfil', profileHint: 'Perfil CMYK para convertir los colores RGB. Arranca en el del documento o en el predeterminado de Affinity.',
    step: 'Redondeo', stepOptions: ['1 %', '5 %', '10 %'],
    inkLimit: 'Límite de tinta', inkLimitHint: 'Suma máxima de las cuatro tintas. Suele ser 300 % en papel estucado, 260 % en papel obra y 240 % en diario.',
    grayK: 'Grises solo con negro', grayKHint: 'Los grises y el negro se imprimen solo con la tinta negra, sin cian, magenta ni amarillo.',
    font: 'Fuente', textSize: 'Tamaño del texto',
    card: 'Fondo', cardHint: 'Color de las fichas, de las etiquetas o del panel detrás de la paleta. Sin color no hay fondo.',
    text: 'Texto', border: 'Borde', borderHint: 'Línea fina alrededor de cada ficha o etiqueta. Sin color no hay borde.',
    large: 'AA grande',
    colourWord: 'Color', strokeWord: 'trazo',
    labels: { hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykEd: 'CMYK EDIT.', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: 'BLANCO', onBlack: 'NEGRO' },
    stats: { one: '1 color', many: '{n} colores', merged: '{n} unidos', capped: 'se muestran {n}' },
    credit: 'Más scripts en visual.af',
  },
  en: {
    noDoc: 'Open a document and select the objects with the colors you want to document.',
    noSel: 'Select the objects with the colors you want to document first. They can be shapes, curves, text or groups.',
    noColours: 'The selection has no readable vector, text or raster colors. Select colored objects or image layers and run the script again.',
    images: 'Include raster images', imagesHint: 'Extract representative colors from selected pixel and image layers. Transparent pixels are ignored.',
    imageQuality: 'Image sampling', imageQualityHint: 'Maximum samples per side of each image. Higher values capture more detail but take longer to process.',
    layout: 'Layout', layoutOptions: ['Cards', 'Columns', 'Circles', 'List', 'Tags'],
    style: 'Style', styleOptions: ['Light', 'Dark', 'Paper', 'Outline', 'Minimal'], size: 'Size',
    sizeHint: 'Width of each swatch. Everything else (text, margins, spacing) is measured in proportion.',
    gSource: 'Colors',
    maxColours: 'Maximum colors', maxColoursHint: 'Sets the maximum number of colors in the palette. If the selection contains fewer distinct colors, only the available colors are used. Limit: 64.', gLayout: 'Arrangement', gCodes: 'Codes', gCmyk: 'CMYK', gText: 'Text and background',
    strokes: 'Include strokes', strokesHint: 'Adds the color of strokes as well as fills.',
    gradients: 'Include gradients', gradientsHint: 'Adds every gradient stop as a color.',
    merge: 'Merge similar', mergeHint: 'Joins colors that are barely distinguishable. At 0 only identical colors are joined; raise it for an illustration with many shades.',
    order: 'Order', orderOptions: ['As on the canvas', 'By hue', 'Dark to light', 'Light to dark', 'Most used first'],
    title: 'Title', titleOptions: ['Layer name', 'Number', 'No title'],
    titleHint: 'With Layer name, the color of an object you renamed in the Layers panel takes that name; the others get a number.',
    position: 'Position', positionOptions: ['Below', 'Right', 'Above', 'Left'],
    perRow: 'Per row', perRowHint: 'How many colors go in each row. At 0 it is worked out for you.',
    spacing: 'Spacing', spacingHint: 'Space between swatches, as a percentage of the size.',
    radius: 'Corners', radiusHint: 'Corner rounding, as a percentage of the size.',
    hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykHint: 'CMYK converted with the chosen profile, not rounded. A color that is already CMYK is shown as it is.',
    cmykEd: 'Print-ready CMYK', cmykEdHint: 'CMYK ready for press: values in steps of 5, no ink below that step, and the four inks added together within the ink limit.',
    hsl: 'HSL', hsb: 'HSB', hsbHint: 'Hue, saturation and brightness, as in the Photoshop and Figma color pickers.',
    lab: 'LAB', labHint: 'L*a*b* with a D50 white point, as in the Affinity Color panel.',
    oklch: 'OKLCH', oklchHint: 'Lightness, chroma and hue in OKLCH, the color format of modern CSS.',
    contrast: 'WCAG contrast', contrastHint: 'Contrast against white and against black, with the level it meets: AAA, AA or AA for large text only.',
    tints: 'Tints', tintsHint: 'Adds the 80, 60, 40 and 20% tints of each color. On a CMYK color the inks are scaled, as on press.',
    profile: 'Profile', profileHint: 'CMYK profile used to convert RGB colors. It starts on the document profile or on the Affinity default.',
    step: 'Rounding', stepOptions: ['1%', '5%', '10%'],
    inkLimit: 'Ink limit', inkLimitHint: 'Maximum total of the four inks. Usually 300% on coated paper, 260% on uncoated and 240% on newsprint.',
    grayK: 'Grays in black only', grayKHint: 'Grays and black print with the black ink only, without cyan, magenta or yellow.',
    font: 'Font', textSize: 'Text size',
    card: 'Background', cardHint: 'Color of the cards, the tags or the panel behind the palette. No color means no background.',
    text: 'Text', border: 'Border', borderHint: 'Thin line around each card or tag. No color means no border.',
    large: 'AA Large',
    colourWord: 'Color', strokeWord: 'stroke',
    labels: { hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykEd: 'CMYK PRINT', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: 'ON WHITE', onBlack: 'ON BLACK' },
    stats: { one: '1 color', many: '{n} colors', merged: '{n} merged', capped: 'showing {n}' },
    credit: 'More scripts at visual.af',
  },
  pt: {
    noDoc: 'Abra um documento e selecione os objetos com as cores que você quer documentar.',
    noSel: 'Selecione primeiro os objetos com as cores que você quer documentar. Podem ser formas, curvas, textos ou grupos.',
    noColours: 'A selecção não tem cores vectoriais, de texto ou de imagens que possam ser lidas. Seleccione objectos com cor ou camadas de imagem e execute o script novamente.',
    images: 'Incluir imagens raster', imagesHint: 'Extrai cores representativas de fotografias e camadas de píxeis. Os píxeis transparentes são ignorados.',
    imageQuality: 'Qualidade da amostragem', imageQualityHint: 'Número máximo de amostras por lado da imagem. Valores maiores captam mais variações, mas exigem mais processamento.',
    layout: 'Disposição', layoutOptions: ['Fichas', 'Colunas', 'Círculos', 'Lista', 'Etiquetas'],
    style: 'Estilo', styleOptions: ['Claro', 'Escuro', 'Papel', 'Contorno', 'Mínimo'], size: 'Tamanho',
    sizeHint: 'Largura de cada amostra. Todo o resto (textos, margens, espaçamento) é medido em proporção.',
    gSource: 'Cores',
    maxColours: 'Máximo de cores', maxColoursHint: 'Define o número máximo de cores a incluir na paleta. Se a selecção tiver menos cores distintas, serão usadas apenas as existentes. Limite: 64.', gLayout: 'Distribuição', gCodes: 'Códigos', gCmyk: 'CMYK', gText: 'Texto e fundo',
    strokes: 'Incluir traços', strokesHint: 'Soma a cor dos traços além da cor dos preenchimentos.',
    gradients: 'Incluir degradês', gradientsHint: 'Soma cada parada dos degradês como uma cor.',
    merge: 'Juntar parecidas', mergeHint: 'Junta as cores que quase não se distinguem. Em 0 só se juntam as idênticas; aumente para uma ilustração com muitos tons.',
    order: 'Ordem', orderOptions: ['Como na tela', 'Por matiz', 'Do escuro ao claro', 'Do claro ao escuro', 'As mais usadas primeiro'],
    title: 'Título', titleOptions: ['Nome da camada', 'Número', 'Sem título'],
    titleHint: 'Com Nome da camada, a cor de um objeto que você renomeou no painel Camadas leva esse nome; as outras levam um número.',
    position: 'Posição', positionOptions: ['Abaixo', 'À direita', 'Acima', 'À esquerda'],
    perRow: 'Por linha', perRowHint: 'Quantas cores vão em cada linha. Em 0 o número é calculado sozinho.',
    spacing: 'Espaçamento', spacingHint: 'Espaço entre as amostras, em porcentagem do tamanho.',
    radius: 'Cantos', radiusHint: 'Arredondamento dos cantos, em porcentagem do tamanho.',
    hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykHint: 'CMYK convertido com o perfil escolhido, sem arredondar. Uma cor que já é CMYK aparece como está.',
    cmykEd: 'CMYK para gráfica', cmykEdHint: 'CMYK pronto para impressão: valores em múltiplos de 5, nenhuma tinta abaixo desse passo e a soma das quatro dentro do limite de tinta.',
    hsl: 'HSL', hsb: 'HSB', hsbHint: 'Matiz, saturação e brilho, como no seletor de cor do Photoshop e do Figma.',
    lab: 'LAB', labHint: 'L*a*b* com branco D50, como no painel Cor do Affinity.',
    oklch: 'OKLCH', oklchHint: 'Luminosidade, croma e matiz em OKLCH, o formato de cor do CSS moderno.',
    contrast: 'Contraste WCAG', contrastHint: 'Contraste com o branco e com o preto, com o nível que atinge: AAA, AA ou AA só para texto grande.',
    tints: 'Tintas claras', tintsHint: 'Acrescenta as versões a 80, 60, 40 e 20 % de cada cor. Numa cor CMYK as tintas diminuem, como na gráfica.',
    profile: 'Perfil', profileHint: 'Perfil CMYK usado para converter as cores RGB. Começa no do documento ou no padrão do Affinity.',
    step: 'Arredondamento', stepOptions: ['1 %', '5 %', '10 %'],
    inkLimit: 'Limite de tinta', inkLimitHint: 'Soma máxima das quatro tintas. Costuma ser 300 % em papel couché, 260 % em papel offset e 240 % em jornal.',
    grayK: 'Cinzas só com preto', grayKHint: 'Os cinzas e o preto são impressos só com a tinta preta, sem ciano, magenta nem amarelo.',
    font: 'Fonte', textSize: 'Tamanho do texto',
    card: 'Fundo', cardHint: 'Cor das fichas, das etiquetas ou do painel atrás da paleta. Sem cor não há fundo.',
    text: 'Texto', border: 'Borda', borderHint: 'Linha fina em volta de cada ficha ou etiqueta. Sem cor não há borda.',
    large: 'AA grande',
    colourWord: 'Cor', strokeWord: 'traço',
    labels: { hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykEd: 'CMYK GRÁF.', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: 'BRANCO', onBlack: 'PRETO' },
    stats: { one: '1 cor', many: '{n} cores', merged: '{n} juntadas', capped: 'mostrando {n}' },
    credit: 'Mais scripts em visual.af',
  },
  ja: {
    noDoc: 'ドキュメントを開いて、記録したい色のオブジェクトを選択してください。',
    noSel: '先に、記録したい色のオブジェクトを選択してください。シェイプ、カーブ、テキスト、グループのどれでもかまいません。',
    noColours: '選択範囲に単色の塗りや線がありません。色の付いたシェイプ、カーブ、テキストを選択してから、もう一度スクリプトを実行してください。',
    layout: 'レイアウト', layoutOptions: ['カード', 'カラム', 'サークル', 'リスト', 'タグ'],
    style: 'スタイル', styleOptions: ['ライト', 'ダーク', 'ペーパー', 'アウトライン', 'ミニマル'], size: 'サイズ',
    sizeHint: '各スウォッチの幅です。テキスト、余白、間隔などはこれに比例して決まります。',
    gSource: 'カラー',
    maxColours: '色数の上限', maxColoursHint: 'パレットに含める色数の上限です。選択範囲に異なる色がそれより少ない場合は、存在する色だけを使用します。上限は64色です。', gLayout: '配置', gCodes: 'コード', gCmyk: 'CMYK', gText: 'テキストと背景',
    strokes: '線を含める', strokesHint: '塗りに加えて、線の色も拾います。',
    gradients: 'グラデーションを含める', gradientsHint: 'グラデーションの各カラー分岐点を1色として拾います。',
    merge: '近い色をまとめる', mergeHint: 'ほとんど見分けのつかない色をまとめます。0では同じ色だけをまとめます。色数の多いイラストでは値を上げてください。',
    order: '並び順', orderOptions: ['キャンバスの並び', '色相順', '暗い順', '明るい順', '使用回数の多い順'],
    title: 'タイトル', titleOptions: ['レイヤー名', '番号', 'タイトルなし'],
    titleHint: 'レイヤー名を選ぶと、レイヤーパネルで名前を付けたオブジェクトの色にはその名前が、それ以外には番号が付きます。',
    position: '位置', positionOptions: ['下', '右', '上', '左'],
    perRow: '1行あたり', perRowHint: '1行に並べる色の数です。0にすると自動で決まります。',
    spacing: '間隔', spacingHint: 'スウォッチ同士の間隔です（サイズに対する割合）。',
    radius: '角の丸み', radiusHint: '角の丸みです（サイズに対する割合）。',
    hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykHint: '選んだプロファイルで変換したCMYKを、丸めずに表示します。もともとCMYKの色はそのまま表示します。',
    cmykEd: '印刷用CMYK', cmykEdHint: '印刷向けのCMYKです。値を5刻みにし、その刻みより小さいインキは0にし、4色の合計をインキ総量の上限内に収めます。',
    hsl: 'HSL', hsb: 'HSB', hsbHint: '色相、彩度、明度。PhotoshopやFigmaのカラーピッカーと同じ表記です。',
    lab: 'LAB', labHint: 'D50白色点のL*a*b*。Affinityのカラーパネルと同じ値です。',
    oklch: 'OKLCH', oklchHint: 'OKLCHの明度、彩度、色相。最近のCSSで使われる色の書式です。',
    contrast: 'WCAGコントラスト', contrastHint: '白と黒に対するコントラスト比と、満たしているレベル（AAA、AA、大きな文字のみAA）を表示します。',
    tints: '濃度違い', tintsHint: '各色の80、60、40、20 %の濃度を加えます。CMYKの色では、印刷と同じくインキの量を下げます。',
    profile: 'プロファイル', profileHint: 'RGBの色をCMYKに変換するプロファイルです。最初はドキュメントのプロファイル、またはAffinityの既定値になります。',
    step: '丸め', stepOptions: ['1 %', '5 %', '10 %'],
    inkLimit: 'インキ総量', inkLimitHint: '4色の合計の上限です。目安はコート紙で300 %、上質紙で260 %、新聞で240 %です。',
    grayK: 'グレーは墨のみ', grayKHint: 'グレーと黒を、シアン、マゼンタ、イエローを使わずに墨（K）だけで刷ります。',
    font: 'フォント', textSize: 'テキストのサイズ',
    card: '背景', cardHint: 'カード、タグ、またはパレットの後ろのパネルの色です。カラーなしにすると背景を付けません。',
    text: 'テキスト', border: '枠線', borderHint: '各カードやタグを囲む細い線です。カラーなしにすると枠線を付けません。',
    large: 'AA（大）',
    colourWord: 'カラー', strokeWord: '線',
    labels: { hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykEd: 'CMYK 印刷', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: '白地', onBlack: '黒地' },
    stats: { one: '1 色', many: '{n} 色', merged: '{n} 色をまとめました', capped: '{n} 色を表示' },
    credit: 'その他のスクリプトは visual.af で',
  },
  id: {
    noDoc: 'Buka dokumen lalu pilih objek dengan warna yang ingin Anda dokumentasikan.',
    noSel: 'Pilih dulu objek dengan warna yang ingin Anda dokumentasikan. Bisa berupa bentuk, kurva, teks, atau grup.',
    noColours: 'Pilihan ini tidak memiliki isian atau garis berwarna solid. Pilih bentuk, kurva, atau teks berwarna, lalu jalankan skrip lagi.',
    layout: 'Tata letak', layoutOptions: ['Kartu', 'Kolom', 'Lingkaran', 'Daftar', 'Label'],
    style: 'Gaya', styleOptions: ['Terang', 'Gelap', 'Kertas', 'Garis tepi', 'Minimal'], size: 'Ukuran',
    sizeHint: 'Lebar setiap sampel warna. Teks, margin, dan jarak lainnya diukur sebanding dengan ini.',
    gSource: 'Warna',
    maxColours: 'Jumlah maksimum warna', maxColoursHint: 'Menentukan jumlah maksimum warna dalam palet. Jika pilihan memiliki lebih sedikit warna yang berbeda, hanya warna yang tersedia yang digunakan. Batas: 64.', gLayout: 'Susunan', gCodes: 'Kode', gCmyk: 'CMYK', gText: 'Teks dan latar',
    strokes: 'Sertakan garis', strokesHint: 'Menambahkan warna garis selain warna isian.',
    gradients: 'Sertakan gradien', gradientsHint: 'Menambahkan setiap titik warna gradien sebagai satu warna.',
    merge: 'Gabungkan yang mirip', mergeHint: 'Menggabungkan warna yang nyaris tidak bisa dibedakan. Di 0 hanya warna yang identik yang digabung; naikkan untuk ilustrasi dengan banyak nuansa.',
    order: 'Urutan', orderOptions: ['Seperti di kanvas', 'Menurut rona', 'Gelap ke terang', 'Terang ke gelap', 'Paling sering dipakai'],
    title: 'Judul', titleOptions: ['Nama layer', 'Nomor', 'Tanpa judul'],
    titleHint: 'Dengan Nama layer, warna dari objek yang Anda beri nama di panel Layer memakai nama itu; yang lain diberi nomor.',
    position: 'Posisi', positionOptions: ['Di bawah', 'Di kanan', 'Di atas', 'Di kiri'],
    perRow: 'Per baris', perRowHint: 'Berapa warna di setiap baris. Di 0 jumlahnya dihitung otomatis.',
    spacing: 'Jarak', spacingHint: 'Jarak antarsampel, dalam persen dari ukuran.',
    radius: 'Sudut', radiusHint: 'Kelengkungan sudut, dalam persen dari ukuran.',
    hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykHint: 'CMYK hasil konversi dengan profil yang dipilih, tanpa dibulatkan. Warna yang sudah CMYK ditampilkan apa adanya.',
    cmykEd: 'CMYK siap cetak', cmykEdHint: 'CMYK untuk percetakan: nilai kelipatan 5, tidak ada tinta di bawah langkah itu, dan jumlah keempat tinta tetap di bawah batas tinta.',
    hsl: 'HSL', hsb: 'HSB', hsbHint: 'Rona, saturasi, dan kecerahan, seperti di pemilih warna Photoshop dan Figma.',
    lab: 'LAB', labHint: 'L*a*b* dengan titik putih D50, seperti di panel Warna Affinity.',
    oklch: 'OKLCH', oklchHint: 'Kecerahan, kroma, dan rona dalam OKLCH, format warna CSS modern.',
    contrast: 'Kontras WCAG', contrastHint: 'Kontras terhadap putih dan hitam, dengan level yang dipenuhi: AAA, AA, atau AA hanya untuk teks besar.',
    tints: 'Tint', tintsHint: 'Menambahkan tint 80, 60, 40, dan 20 % dari setiap warna. Pada warna CMYK, tintanya dikurangi seperti di percetakan.',
    profile: 'Profil', profileHint: 'Profil CMYK untuk mengonversi warna RGB. Awalnya profil dokumen atau profil bawaan Affinity.',
    step: 'Pembulatan', stepOptions: ['1 %', '5 %', '10 %'],
    inkLimit: 'Batas tinta', inkLimitHint: 'Jumlah maksimum keempat tinta. Biasanya 300 % untuk kertas coated, 260 % untuk uncoated, dan 240 % untuk koran.',
    grayK: 'Abu-abu hanya hitam', grayKHint: 'Abu-abu dan hitam dicetak hanya dengan tinta hitam, tanpa cyan, magenta, atau kuning.',
    font: 'Font', textSize: 'Ukuran teks',
    card: 'Latar', cardHint: 'Warna kartu, label, atau panel di belakang palet. Tanpa warna berarti tanpa latar.',
    text: 'Teks', border: 'Tepi', borderHint: 'Garis tipis di sekeliling setiap kartu atau label. Tanpa warna berarti tanpa tepi.',
    large: 'AA besar',
    colourWord: 'Warna', strokeWord: 'garis',
    labels: { hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykEd: 'CMYK CETAK', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: 'DI PUTIH', onBlack: 'DI HITAM' },
    stats: { one: '1 warna', many: '{n} warna', merged: '{n} digabung', capped: 'menampilkan {n}' },
    credit: 'Skrip lainnya di visual.af',
  },
  nl: {
    noDoc: 'Open een document en selecteer de objecten met de kleuren die je wilt vastleggen.',
    noSel: 'Selecteer eerst de objecten met de kleuren die je wilt vastleggen. Dat kunnen vormen, curves, tekst of groepen zijn.',
    noColours: 'De selectie heeft geen effen vullingen of lijnen. Selecteer vormen, curves of tekst met kleur en voer het script opnieuw uit.',
    layout: 'Indeling', layoutOptions: ['Kaarten', 'Kolommen', 'Cirkels', 'Lijst', 'Labels'],
    style: 'Stijl', styleOptions: ['Licht', 'Donker', 'Papier', 'Omtrek', 'Minimaal'], size: 'Grootte',
    sizeHint: 'Breedte van elk staal. De rest (tekst, marges, tussenruimte) schaalt mee.',
    gSource: 'Kleuren',
    maxColours: 'Maximum aantal kleuren', maxColoursHint: 'Stelt het maximumaantal kleuren in het palet in. Bevat de selectie minder verschillende kleuren, dan worden alleen die kleuren gebruikt. Limiet: 64.', gLayout: 'Schikking', gCodes: 'Codes', gCmyk: 'CMYK', gText: 'Tekst en achtergrond',
    strokes: 'Lijnen meenemen', strokesHint: 'Neemt naast de vullingen ook de kleur van lijnen op.',
    gradients: 'Verlopen meenemen', gradientsHint: 'Neemt elk punt van een verloop op als kleur.',
    merge: 'Gelijke samenvoegen', mergeHint: 'Voegt kleuren samen die nauwelijks van elkaar te onderscheiden zijn. Op 0 worden alleen identieke kleuren samengevoegd; zet de waarde hoger voor een illustratie met veel nuances.',
    order: 'Volgorde', orderOptions: ['Zoals op het canvas', 'Op kleurtoon', 'Van donker naar licht', 'Van licht naar donker', 'Meest gebruikt eerst'],
    title: 'Titel', titleOptions: ['Laagnaam', 'Nummer', 'Geen titel'],
    titleHint: 'Met Laagnaam krijgt de kleur van een object dat je in het paneel Lagen een naam hebt gegeven die naam; de andere krijgen een nummer.',
    position: 'Positie', positionOptions: ['Onder', 'Rechts', 'Boven', 'Links'],
    perRow: 'Per rij', perRowHint: 'Hoeveel kleuren er in elke rij komen. Op 0 wordt dat voor je berekend.',
    spacing: 'Tussenruimte', spacingHint: 'Ruimte tussen de stalen, als percentage van de grootte.',
    radius: 'Hoeken', radiusHint: 'Afronding van de hoeken, als percentage van de grootte.',
    hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykHint: 'CMYK omgezet met het gekozen profiel, niet afgerond. Een kleur die al CMYK is, wordt getoond zoals hij is.',
    cmykEd: 'CMYK voor drukwerk', cmykEdHint: 'CMYK klaar voor de drukker: waarden in stappen van 5, geen inkt onder die stap en de vier inkten samen binnen de inktlimiet.',
    hsl: 'HSL', hsb: 'HSB', hsbHint: 'Kleurtoon, verzadiging en helderheid, zoals in de kleurkiezers van Photoshop en Figma.',
    lab: 'LAB', labHint: 'L*a*b* met een D50-witpunt, zoals in het paneel Kleur van Affinity.',
    oklch: 'OKLCH', oklchHint: 'Helderheid, chroma en kleurtoon in OKLCH, het kleurformaat van moderne CSS.',
    contrast: 'WCAG-contrast', contrastHint: 'Contrast met wit en met zwart, met het niveau dat gehaald wordt: AAA, AA of AA alleen voor grote tekst.',
    tints: 'Tinten', tintsHint: 'Voegt de tinten van 80, 60, 40 en 20% van elke kleur toe. Bij een CMYK-kleur worden de inkten geschaald, zoals op de pers.',
    profile: 'Profiel', profileHint: 'CMYK-profiel waarmee RGB-kleuren worden omgezet. Het begint op het profiel van het document of op de standaard van Affinity.',
    step: 'Afronding', stepOptions: ['1%', '5%', '10%'],
    inkLimit: 'Inktlimiet', inkLimitHint: 'Maximaal totaal van de vier inkten. Meestal 300% op gestreken papier, 260% op ongestreken papier en 240% op krantenpapier.',
    grayK: 'Grijs alleen in zwart', grayKHint: 'Grijstinten en zwart worden alleen met zwarte inkt gedrukt, zonder cyaan, magenta of geel.',
    font: 'Lettertype', textSize: 'Tekstgrootte',
    card: 'Achtergrond', cardHint: 'Kleur van de kaarten, de labels of het paneel achter het palet. Geen kleur betekent geen achtergrond.',
    text: 'Tekst', border: 'Rand', borderHint: 'Dunne lijn rond elke kaart of elk label. Geen kleur betekent geen rand.',
    large: 'AA groot',
    colourWord: 'Kleur', strokeWord: 'lijn',
    labels: { hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykEd: 'CMYK DRUK', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: 'OP WIT', onBlack: 'OP ZWART' },
    stats: { one: '1 kleur', many: '{n} kleuren', merged: '{n} samengevoegd', capped: '{n} getoond' },
    credit: 'Meer scripts op visual.af',
  },
  de: { noDoc: 'Öffne ein Dokument und wähle eine Ebene aus.',
    noSel: 'Wähle die Ebene aus, auf die du den Effekt anwenden möchtest.',
    noColours: 'Die Auswahl hat keine Füllungen oder Konturen in Volltonfarbe. Wähle Formen, Kurven oder Text mit Farbe aus und führe das Skript erneut aus.',
    layout: 'Layout', layoutOptions: ['Karten', 'Spalten', 'Kreise', 'Liste', 'Etiketten'], style: 'Stil',
    styleOptions: ['Hell', 'Dunkel', 'Papier', 'Kontur', 'Minimal'], size: 'Größe',
    sizeHint: 'Breite jedes Farbfelds. Alles andere (Text, Ränder, Abstände) wird im Verhältnis dazu bemessen.',
    gSource: 'Farben',
    maxColours: 'Maximale Farbanzahl', maxColoursHint: 'Legt die maximale Anzahl der Farben in der Palette fest. Enthält die Auswahl weniger unterschiedliche Farben, werden nur die vorhandenen Farben verwendet. Grenze: 64.', gLayout: 'Anordnung', gCodes: 'Codes', gCmyk: 'CMYK', gText: 'Text und Hintergrund',
    strokes: 'Konturen einbeziehen', strokesHint: 'Fügt neben den Füllungen auch die Farbe der Konturen hinzu.',
    gradients: 'Verläufe einbeziehen', gradientsHint: 'Fügt jeden Farbstopp der Verläufe als Farbe hinzu.',
    merge: 'Ähnliche zusammenführen',
    mergeHint: 'Fasst Farben zusammen, die sich kaum unterscheiden lassen. Bei 0 werden nur identische zusammengefasst; erhöhe den Wert bei einer Illustration mit vielen Abstufungen.',
    order: 'Reihenfolge',
    orderOptions: ['Wie auf der Arbeitsfläche', 'Nach Farbton', 'Von dunkel nach hell', 'Von hell nach dunkel', 'Häufigste zuerst'],
    title: 'Titel', titleOptions: ['Ebenenname', 'Nummer', 'Kein Titel'],
    titleHint: 'Bei „Ebenenname“ trägt die Farbe eines Objekts, das du im Ebenen-Panel umbenannt hast, diesen Namen; die anderen bekommen eine Nummer.',
    position: 'Position', positionOptions: ['Darunter', 'Rechts', 'Darüber', 'Links'], perRow: 'Pro Zeile',
    perRowHint: 'Wie viele Farben in jede Zeile kommen. Bei 0 wird das automatisch berechnet.', spacing: 'Abstand',
    spacingHint: 'Abstand zwischen den Farbfeldern, in Prozent der Größe.', radius: 'Ecken',
    radiusHint: 'Rundung der Ecken, in Prozent der Größe.', hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK',
    cmykHint: 'CMYK, mit dem gewählten Profil umgerechnet und nicht gerundet. Eine Farbe, die schon CMYK ist, wird unverändert angezeigt.',
    cmykEd: 'Druckfertiges CMYK',
    cmykEdHint: 'CMYK für den Druck: Werte in 5er-Schritten, keine Druckfarbe unter diesem Schritt und die Summe der vier Druckfarben innerhalb des Gesamtfarbauftrags.',
    hsl: 'HSL', hsb: 'HSB',
    hsbHint: 'Farbton, Sättigung und Helligkeit, wie in den Farbwählern von Photoshop und Figma.', lab: 'LAB',
    labHint: 'L*a*b* mit D50-Weißpunkt, wie im Farb-Panel von Affinity.', oklch: 'OKLCH',
    oklchHint: 'Helligkeit, Chroma und Farbton in OKLCH, dem Farbformat von modernem CSS.', contrast: 'WCAG-Kontrast',
    contrastHint: 'Kontrast gegen Weiß und gegen Schwarz, mit der erreichten Stufe: AAA, AA oder AA nur für großen Text.',
    tints: 'Abstufungen',
    tintsHint: 'Fügt die Abstufungen zu 80, 60, 40 und 20 % jeder Farbe hinzu. Bei einer CMYK-Farbe werden die Druckfarben reduziert, wie im Druck.',
    profile: 'Profil',
    profileHint: 'CMYK-Profil zum Umrechnen der RGB-Farben. Am Anfang ist das Profil des Dokuments oder der Standard von Affinity eingestellt.',
    step: 'Rundung', stepOptions: ['1 %', '5 %', '10 %'], inkLimit: 'Gesamtfarbauftrag',
    inkLimitHint: 'Höchste Summe der vier Druckfarben. Meist 300 % bei gestrichenem Papier, 260 % bei ungestrichenem und 240 % bei Zeitungspapier.',
    grayK: 'Grau nur mit Schwarz',
    grayKHint: 'Grautöne und Schwarz werden nur mit schwarzer Druckfarbe gedruckt, ohne Cyan, Magenta oder Gelb.',
    font: 'Schrift', textSize: 'Textgröße', card: 'Hintergrund',
    cardHint: 'Farbe der Karten, der Etiketten oder der Fläche hinter der Palette. Keine Farbe bedeutet kein Hintergrund.',
    text: 'Text', border: 'Rand',
    borderHint: 'Dünne Linie um jede Karte oder jedes Etikett. Keine Farbe bedeutet kein Rand.', large: 'AA groß',
    colourWord: 'Farbe', strokeWord: 'Kontur',
    labels: { hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykEd: 'CMYK DRUCK', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: 'AUF WEISS', onBlack: 'AUF SCHWARZ' },
    stats: { one: '1 Farbe', many: '{n} Farben', merged: '{n} zusammengeführt', capped: '{n} angezeigt' },
    credit: 'Mehr Effekte auf visual.af' },
  fr: { noDoc: 'Ouvrez un document et sélectionnez les objets dont vous voulez documenter les couleurs.',
    noSel: 'Sélectionnez d’abord les objets dont vous voulez documenter les couleurs. Il peut s’agir de formes, de courbes, de textes ou de groupes.',
    noColours: 'La sélection n’a ni remplissage ni contour de couleur unie. Sélectionnez des formes, des courbes ou des textes en couleur, puis relancez le script.',
    layout: 'Disposition', layoutOptions: ['Fiches', 'Colonnes', 'Cercles', 'Liste', 'Étiquettes'], style: 'Style',
    styleOptions: ['Clair', 'Sombre', 'Papier', 'Contour', 'Minimal'], size: 'Taille',
    sizeHint: 'Largeur de chaque échantillon. Tout le reste (textes, marges, espacement) est proportionnel.',
    gSource: 'Couleurs',
    maxColours: 'Nombre maximal de couleurs', maxColoursHint: 'Définit le nombre maximal de couleurs de la palette. Si la sélection contient moins de couleurs différentes, seules les couleurs disponibles sont utilisées. Limite : 64.', gLayout: 'Agencement', gCodes: 'Codes', gCmyk: 'CMJN', gText: 'Texte et arrière-plan',
    strokes: 'Inclure les contours', strokesHint: 'Ajoute la couleur des contours en plus de celle des remplissages.',
    gradients: 'Inclure les dégradés',
    gradientsHint: 'Ajoute chaque point de couleur des dégradés comme une couleur.',
    merge: 'Fusionner les couleurs proches',
    mergeHint: 'Regroupe les couleurs presque impossibles à distinguer. À 0, seules les couleurs identiques sont regroupées ; augmentez la valeur pour une illustration avec beaucoup de nuances.',
    order: 'Ordre',
    orderOptions: ['Comme dans le document', 'Par teinte', 'Du foncé au clair', 'Du clair au foncé', 'Les plus utilisées d’abord'],
    title: 'Titre', titleOptions: ['Nom du calque', 'Numéro', 'Sans titre'],
    titleHint: 'Avec « Nom du calque », la couleur d’un objet que vous avez renommé dans le panneau Calques prend ce nom ; les autres reçoivent un numéro.',
    position: 'Position', positionOptions: ['Dessous', 'À droite', 'Dessus', 'À gauche'], perRow: 'Par ligne',
    perRowHint: 'Nombre de couleurs sur chaque ligne. À 0, il est calculé automatiquement.', spacing: 'Espacement',
    spacingHint: 'Espace entre les échantillons, en pourcentage de la taille.', radius: 'Coins',
    radiusHint: 'Arrondi des coins, en pourcentage de la taille.', hex: 'HEX', rgb: 'RVB', cmyk: 'CMJN',
    cmykHint: 'CMJN converti avec le profil choisi, sans arrondi. Une couleur déjà en CMJN s’affiche telle quelle.',
    cmykEd: 'CMJN pour l’impression',
    cmykEdHint: 'CMJN prêt pour l’imprimeur : valeurs par pas de 5, aucune encre sous ce pas, et la somme des quatre encres dans la limite d’encrage.',
    hsl: 'HSL', hsb: 'HSB',
    hsbHint: 'Teinte, saturation et luminosité, comme dans les sélecteurs de couleur de Photoshop et de Figma.',
    lab: 'LAB', labHint: 'L*a*b* avec un point blanc D50, comme dans le panneau Couleur d’Affinity.', oklch: 'OKLCH',
    oklchHint: 'Luminosité, chroma et teinte en OKLCH, le format de couleur du CSS moderne.',
    contrast: 'Contraste WCAG',
    contrastHint: 'Contraste sur blanc et sur noir, avec le niveau atteint : AAA, AA ou AA pour grand texte seulement.',
    tints: 'Teintes',
    tintsHint: 'Ajoute les teintes à 80, 60, 40 et 20 % de chaque couleur. Sur une couleur CMJN, les encres sont réduites, comme à l’impression.',
    profile: 'Profil',
    profileHint: 'Profil CMJN pour convertir les couleurs RVB. Au départ, celui du document ou celui d’Affinity par défaut.',
    step: 'Arrondi', stepOptions: ['1 %', '5 %', '10 %'], inkLimit: 'Limite d’encrage',
    inkLimitHint: 'Somme maximale des quatre encres. En général, 300 % sur papier couché, 260 % sur papier non couché et 240 % sur papier journal.',
    grayK: 'Gris en noir seul',
    grayKHint: 'Les gris et le noir s’impriment uniquement avec l’encre noire, sans cyan, magenta ni jaune.',
    font: 'Police', textSize: 'Taille du texte', card: 'Arrière-plan',
    cardHint: 'Couleur des fiches, des étiquettes ou du panneau derrière la palette. Sans couleur, pas d’arrière-plan.',
    text: 'Texte', border: 'Bordure',
    borderHint: 'Fine ligne autour de chaque fiche ou étiquette. Sans couleur, pas de bordure.', large: 'AA grand',
    colourWord: 'Couleur', strokeWord: 'contour',
    labels: { hex: 'HEX', rgb: 'RVB', cmyk: 'CMJN', cmykEd: 'CMJN IMPR.', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: 'SUR BLANC', onBlack: 'SUR NOIR' },
    stats: { one: '1 couleur', many: '{n} couleurs', merged: '{n} fusionnées', capped: '{n} affichées' },
    credit: 'Plus de scripts sur visual.af' },
  th: { noDoc: 'เปิดเอกสาร แล้วเลือกวัตถุที่มีสีที่คุณต้องการแสดงรหัส',
    noSel: 'เลือกวัตถุที่มีสีที่คุณต้องการแสดงรหัสก่อน อาจเป็นรูปทรง เส้นโค้ง ข้อความ หรือกลุ่มก็ได้',
    noColours: 'สิ่งที่เลือกไม่มีสีเติมหรือเส้นขอบที่เป็นสีทึบ เลือกรูปทรง เส้นโค้ง หรือข้อความที่มีสี แล้วเรียกใช้สคริปต์อีกครั้ง',
    layout: 'เค้าโครง', layoutOptions: ['การ์ด', 'คอลัมน์', 'วงกลม', 'รายการ', 'ป้าย'], style: 'สไตล์',
    styleOptions: ['สว่าง', 'มืด', 'กระดาษ', 'เส้นกรอบ', 'มินิมอล'], size: 'ขนาด',
    sizeHint: 'ความกว้างของตัวอย่างสีแต่ละอัน ส่วนอื่นทั้งหมด (ข้อความ ระยะขอบ ระยะห่าง) จะปรับตามสัดส่วน',
    gSource: 'สี',
    maxColours: 'จำนวนสีสูงสุด', maxColoursHint: 'กำหนดจำนวนสีสูงสุดในชุดสี หากสิ่งที่เลือกมีสีที่แตกต่างกันน้อยกว่าจำนวนนี้ จะใช้เฉพาะสีที่มีอยู่ ขีดจำกัด: 64 สี.', gLayout: 'การจัดวาง', gCodes: 'รหัส', gCmyk: 'CMYK', gText: 'ข้อความและพื้นหลัง',
    strokes: 'รวมเส้นขอบ', strokesHint: 'เพิ่มสีของเส้นขอบ นอกเหนือจากสีเติม', gradients: 'รวมการไล่สี',
    gradientsHint: 'เพิ่มจุดสีทุกจุดของการไล่สีเป็นสีหนึ่งสี', merge: 'รวมสีที่คล้ายกัน',
    mergeHint: 'รวมสีที่แทบแยกไม่ออก เมื่อเป็น 0 จะรวมเฉพาะสีที่เหมือนกันทุกประการ เพิ่มค่านี้สำหรับภาพประกอบที่มีเฉดสีจำนวนมาก',
    order: 'ลำดับ', orderOptions: ['ตามตำแหน่งบนแคนวาส', 'ตามเฉดสี', 'มืดไปสว่าง', 'สว่างไปมืด', 'ใช้มากที่สุดก่อน'],
    title: 'ชื่อ', titleOptions: ['ชื่อเลเยอร์', 'ตัวเลข', 'ไม่มีชื่อ'],
    titleHint: 'เมื่อเลือก “ชื่อเลเยอร์” สีของวัตถุที่คุณเปลี่ยนชื่อในแผง Layers จะใช้ชื่อนั้น ส่วนสีอื่นจะได้เป็นตัวเลข',
    position: 'ตำแหน่ง', positionOptions: ['ด้านล่าง', 'ด้านขวา', 'ด้านบน', 'ด้านซ้าย'], perRow: 'ต่อแถว',
    perRowHint: 'จำนวนสีในแต่ละแถว เมื่อเป็น 0 จะคำนวณให้อัตโนมัติ', spacing: 'ระยะห่าง',
    spacingHint: 'ระยะห่างระหว่างตัวอย่างสี เป็นเปอร์เซ็นต์ของขนาด', radius: 'มุม',
    radiusHint: 'ความมนของมุม เป็นเปอร์เซ็นต์ของขนาด', hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK',
    cmykHint: 'CMYK ที่แปลงด้วยโปรไฟล์ที่เลือก โดยไม่ปัดเศษ สีที่เป็น CMYK อยู่แล้วจะแสดงตามเดิม',
    cmykEd: 'CMYK พร้อมพิมพ์',
    cmykEdHint: 'CMYK พร้อมส่งโรงพิมพ์: ค่าเป็นขั้นละ 5 ไม่มีหมึกที่ต่ำกว่าขั้นนั้น และผลรวมของหมึกทั้งสี่สีอยู่ภายในขีดจำกัดหมึก',
    hsl: 'HSL', hsb: 'HSB', hsbHint: 'เฉดสี ความอิ่มตัว และความสว่าง เหมือนในตัวเลือกสีของ Photoshop และ Figma',
    lab: 'LAB', labHint: 'L*a*b* ที่จุดขาว D50 เหมือนในแผง Color ของ Affinity', oklch: 'OKLCH',
    oklchHint: 'ความสว่าง โครมา และเฉดสีใน OKLCH ซึ่งเป็นรูปแบบสีของ CSS สมัยใหม่', contrast: 'คอนทราสต์ WCAG',
    contrastHint: 'คอนทราสต์เทียบกับสีขาวและสีดำ พร้อมระดับที่ผ่าน: AAA, AA หรือ AA เฉพาะข้อความขนาดใหญ่',
    tints: 'สีอ่อน',
    tintsHint: 'เพิ่มสีอ่อนที่ 80, 60, 40 และ 20% ของแต่ละสี สำหรับสี CMYK หมึกจะลดลงตามสัดส่วน เหมือนในงานพิมพ์',
    profile: 'โปรไฟล์',
    profileHint: 'โปรไฟล์ CMYK ที่ใช้แปลงสี RGB เริ่มต้นจะเป็นโปรไฟล์ของเอกสาร หรือค่าเริ่มต้นของ Affinity',
    step: 'การปัดเศษ', stepOptions: ['1%', '5%', '10%'], inkLimit: 'ขีดจำกัดหมึก',
    inkLimitHint: 'ผลรวมสูงสุดของหมึกทั้งสี่สี โดยทั่วไปคือ 300% บนกระดาษเคลือบ 260% บนกระดาษไม่เคลือบ และ 240% บนกระดาษหนังสือพิมพ์',
    grayK: 'สีเทาด้วยหมึกดำเท่านั้น', grayKHint: 'สีเทาและสีดำพิมพ์ด้วยหมึกดำเท่านั้น ไม่มีไซแอน มาเจนตา หรือเหลือง',
    font: 'ฟอนต์', textSize: 'ขนาดข้อความ', card: 'พื้นหลัง',
    cardHint: 'สีของการ์ด ป้าย หรือแผงด้านหลังชุดสี ไม่มีสีหมายถึงไม่มีพื้นหลัง', text: 'ข้อความ', border: 'กรอบ',
    borderHint: 'เส้นบาง ๆ รอบการ์ดหรือป้ายแต่ละอัน ไม่มีสีหมายถึงไม่มีกรอบ', large: 'AA ตัวใหญ่', colourWord: 'สี',
    strokeWord: 'เส้นขอบ',
    labels: { hex: 'HEX', rgb: 'RGB', cmyk: 'CMYK', cmykEd: 'CMYK พิมพ์', hsl: 'HSL', hsb: 'HSB', lab: 'LAB', oklch: 'OKLCH', onWhite: 'บนสีขาว', onBlack: 'บนสีดำ' },
    stats: { one: '1 สี', many: '{n} สี', merged: 'รวม {n} สี', capped: 'แสดง {n} สี' },
    credit: 'สคริปต์อื่น ๆ ที่ visual.af' },
};

function layoutPalette(recs, lines, titles, p, W, look, mw, cap) {
  const M = textMetrics(W, p);
  const L = LAYOUTS[p.layout].key;
  const n = recs.length;
  const G = W * p.spacing / 100, R = W * p.radius / 100, pad = W * 0.08;
  const hair = Math.max(0.5, W * 0.005);
  const items = [];
  const shape = (curve, fill, g, stroke) => items.push({ k: 'shape', curve, fill, g, stroke: stroke || null, weight: hair });
  const text = (spec, x, y, g) => items.push({ k: 'text', spec, x, y, g });
  const anyTitle = titles.some((t) => t);

  const nLines = lines.length ? lines[0].length : 0;
  const capC = cap * M.fsC, capT = cap * M.fsT;
  const labelsW = Math.max(0, ...lines.map((ls) => Math.max(0, ...ls.map((l) => mw(FontWeight.Normal, 0, l[0]) * M.fsL))));
  const valuesW = (i) => Math.max(0, ...lines[i].map((l) => mw(FontWeight.Medium, 0, l[1]) * M.fsC));
  const colGap = M.fsC * 1.1;
  const hasText = anyTitle || nLines > 0;
  const blockH = (anyTitle ? capT + (nLines ? M.gapTitle : M.fsT * 0.22) : 0) + (nLines ? capC + (nLines - 1) * M.lead + M.fsC * 0.28 : 0);
  const blockW = (i) => Math.max(titles[i] ? mw(FontWeight.Bold, 0, titles[i]) * M.fsT : 0, nLines ? labelsW + colGap + valuesW(i) : 0);
  const maxBlockW = Math.max(0, ...recs.map((r, i) => blockW(i)));
  const drawBlock = (i, x, y, ink, centred, g) => {
    const c = ink.concat(255);
    const bw = centred ? blockW(i) : 0;
    const left = centred ? x - bw / 2 : x;
    let base = y;
    if (anyTitle) {
      base += capT;
      if (titles[i]) {
        text({ align: centred ? 1 : 0, lead: M.lead, lines: [[{ t: titles[i], w: FontWeight.Bold, s: M.fsT, c }]] }, centred ? x : left, base, g);
      }
      base += M.gapTitle;
    }
    if (nLines) {
      base += capC;
      const b = blockSpec(lines[i], M, { text: ink });
      text(b.labels, left, base, g);
      text(b.values, left + labelsW + colGap, base, g);
    }
  };
  const tintLabel = (rgb, t, x, y, g) => {
    const s = M.fsTint;
    text({ align: 0, lead: M.lead, lines: [[{ t: Math.round(t * 100) + '%', w: FontWeight.Medium, s, c: inkOn(tintRGB(rgb, t)).concat(230) }]] }, x, y, g);
  };

  let cols = p.perRow > 0 ? p.perRow : L === 'list' ? Math.ceil(n / 10) : n <= 8 ? n : Math.ceil(n / Math.ceil(n / 6));
  cols = Math.max(1, Math.min(cols, n));
  const rows = Math.ceil(n / cols);
  const card = look.card, border = look.border;

  if (L === 'cards') {
    const cw = Math.max(W, maxBlockW + 2 * pad), chipH = cw * 0.72, tintH = p.tints ? cw * 0.17 : 0;
    const ch = chipH + tintH + (hasText ? pad + blockH + pad : 0);
    recs.forEach((rec, i) => {
      const x = (i % cols) * (cw + G), y = Math.floor(i / cols) * (ch + G);
      const framed = !!card || !!border;
      if (framed) shape(roundRect(x, y, cw, ch, [R, R, R, R]), card, i, border);
      shape(roundRect(x, y, cw, chipH, (framed && hasText) || p.tints ? [R, R, 0, 0] : [R, R, R, R]), rec.colour, i);
      if (p.tints) {
        const tw = cw / TINTS.length, last = TINTS.length - 1;
        TINTS.forEach((t, j) => {
          const rr = hasText ? 0 : R;
          shape(roundRect(x + j * tw, y + chipH, tw, tintH, [0, 0, j === last ? rr : 0, j === 0 ? rr : 0]), tintColour(rec, t), i);
          tintLabel(rec.rgb, t, x + j * tw + tw * 0.12, y + chipH + tintH * 0.5 + cap * M.fsTint * 0.5, i);
        });
      }
      if (hasText) drawBlock(i, x + pad, y + chipH + tintH + pad, look.text, false, i);
    });
    return { items, w: cols * cw + (cols - 1) * G, h: rows * ch + (rows - 1) * G };
  }

  if (L === 'columns') {
    const cw = Math.max(W, maxBlockW + 2 * pad), tintH = p.tints ? W * 0.2 : 0;
    const ch = Math.max(W * 2.2, pad + blockH + pad * 3 + TINTS.length * tintH);
    recs.forEach((rec, i) => {
      const x = (i % cols) * (cw + G), y = Math.floor(i / cols) * (ch + G);
      const first = i % cols === 0, last = i % cols === cols - 1 || i === n - 1;
      const rr = G > 0 ? [R, R, R, R] : [first ? R : 0, last ? R : 0, last ? R : 0, first ? R : 0];
      const bodyH = ch - TINTS.length * tintH;
      shape(roundRect(x, y, cw, p.tints ? bodyH : ch, p.tints ? [rr[0], rr[1], 0, 0] : rr), rec.colour, i);
      if (p.tints) {
        TINTS.forEach((t, j) => {
          const ty = y + bodyH + j * tintH, lastT = j === TINTS.length - 1;
          shape(roundRect(x, ty, cw, tintH, lastT ? [0, 0, rr[2], rr[3]] : [0, 0, 0, 0]), tintColour(rec, t), i);
          tintLabel(rec.rgb, t, x + pad, ty + tintH * 0.5 + cap * M.fsTint * 0.5, i);
        });
      }
      drawBlock(i, x + pad, y + bodyH - pad - blockH, inkOn(rec.rgb), false, i);
    });
    return { items, w: cols * cw + (cols - 1) * G, h: rows * ch + (rows - 1) * G };
  }

  if (L === 'circles') {
    const cw = Math.max(W, maxBlockW), d = W;
    const tg = W * 0.05, td = p.tints ? (W - (TINTS.length - 1) * tg) / TINTS.length : 0;
    const tintsH = p.tints ? W * 0.07 + td : 0;
    const ch = d + tintsH + (hasText ? W * 0.12 + blockH : 0);
    const panelPad = card ? W * 0.18 : 0;
    const ox = panelPad, oy = panelPad;
    const pw = cols * cw + (cols - 1) * G, ph = rows * ch + (rows - 1) * G;
    if (card || border) shape(roundRect(0, 0, pw + 2 * panelPad, ph + 2 * panelPad, [R, R, R, R]), card, -1, border);
    recs.forEach((rec, i) => {
      const x = ox + (i % cols) * (cw + G), y = oy + Math.floor(i / cols) * (ch + G), cx = x + cw / 2;
      shape(Curve.createEllipse({ x: cx - d / 2, y, width: d, height: d }), rec.colour, i);
      if (p.tints) {
        TINTS.forEach((t, j) => {
          shape(Curve.createEllipse({ x: cx - d / 2 + j * (td + tg), y: y + d + W * 0.07, width: td, height: td }), tintColour(rec, t), i);
        });
      }
      drawBlock(i, cx, y + d + tintsH + W * 0.12, look.text, true, i);
    });
    return { items, w: pw + 2 * panelPad, h: ph + 2 * panelPad };
  }

  if (L === 'list') {
    const S = W * 0.42, gapX = W * 0.12;
    const tintH = p.tints ? S * 0.26 : 0;
    const rowH = Math.max(S + tintH, blockH);
    const itemW = S + gapX + maxBlockW, colGapW = W * 0.35;
    const perCol = Math.ceil(n / cols);
    const panelPad = card ? W * 0.16 : 0;
    const pw = cols * itemW + (cols - 1) * colGapW, ph = perCol * rowH + (perCol - 1) * G;
    if (card || border) shape(roundRect(0, 0, pw + 2 * panelPad, ph + 2 * panelPad, [R, R, R, R]), card, -1, border);
    recs.forEach((rec, i) => {
      const x = panelPad + Math.floor(i / perCol) * (itemW + colGapW), y = panelPad + (i % perCol) * (rowH + G);
      shape(roundRect(x, y, S, S, p.tints ? [R * 0.42, R * 0.42, 0, 0] : [R * 0.42, R * 0.42, R * 0.42, R * 0.42]), rec.colour, i);
      if (p.tints) {
        const tw = S / TINTS.length;
        TINTS.forEach((t, j) => {
          const rr = R * 0.42, rad = [0, 0, j === TINTS.length - 1 ? rr : 0, j === 0 ? rr : 0];
          shape(roundRect(x + j * tw, y + S, tw, tintH, rad), tintColour(rec, t), i);
        });
      }
      drawBlock(i, x + S + gapX, y, look.text, false, i);
    });
    return { items, w: pw + 2 * panelPad, h: ph + 2 * panelPad };
  }
  return { items, w: 0, h: 0 };
}

function layoutTags(groupsIn, recs, lines, titles, p, W, look, mw, cap) {
  const M = textMetrics(W, p);
  const pad = W * 0.07, G = W * p.spacing / 100;
  const hair = Math.max(0.5, W * 0.005);
  const items = [];
  const nLines = lines.length ? lines[0].length : 0;
  const capC = cap * M.fsC, capT = cap * M.fsT;
  const labelsW = Math.max(0, ...lines.map((ls) => Math.max(0, ...ls.map((l) => mw(FontWeight.Normal, 0, l[0]) * M.fsL))));
  const colGap = M.fsC * 1.1, S = M.fsC * 2.4;
  const R = Math.min(W * p.radius / 100, pad + S * 0.18);
  const entryH = Math.max(S, nLines ? capC + (nLines - 1) * M.lead + M.fsC * 0.28 : 0);
  const ink = look.text;
  const tags = groupsIn.map((gr) => {
    const name = gr.title;
    const w0 = Math.max(0, ...gr.recs.map((i) => S + (nLines ? M.fsC * 0.9 + labelsW + colGap + Math.max(0, ...lines[i].map((l) => mw(FontWeight.Medium, 0, l[1]) * M.fsC)) : 0)));
    const tw = Math.max(w0, name ? mw(FontWeight.Bold, 0, name) * M.fsT : 0) + 2 * pad;
    const th = 2 * pad + (name ? capT + M.gapTitle : 0) + gr.recs.length * entryH + (gr.recs.length - 1) * G;
    return { gr, name, tw, th };
  });
  const off = W * 0.3;
  const U = groupsIn.reduce((u, gr) => ({ x0: Math.min(u.x0, gr.box.x), y0: Math.min(u.y0, gr.box.y), x1: Math.max(u.x1, gr.box.x + gr.box.width), y1: Math.max(u.y1, gr.box.y + gr.box.height) }), { x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity });
  const ORD = [[0, 2, 1, 3], [1, 3, 0, 2], [2, 0, 1, 3], [3, 1, 0, 2]][p.position];
  const OPP = [2, 3, 0, 1];
  const tieStep = W * 0.05;
  for (const t of tags) {
    const bx = t.gr.box;
    t.cx = bx.x + bx.width / 2;
    t.cy = bx.y + bx.height / 2;
    t.gaps = [U.y1 - (bx.y + bx.height), U.x1 - (bx.x + bx.width), bx.y - U.y0, bx.x - U.x0];
    t.side = ORD.slice().sort((u, v) => Math.round(t.gaps[u] / tieStep) - Math.round(t.gaps[v] / tieStep) || ORD.indexOf(u) - ORD.indexOf(v))[0];
  }
  const ext = (t, side) => (side % 2 === 0 ? t.tw : t.th);
  const at = (t, side) => (side % 2 === 0 ? t.cx : t.cy);
  for (const [s0, s1] of [[0, 2], [1, 3]]) {
    const end = { [s0]: -Infinity, [s1]: -Infinity };
    for (const t of tags.filter((x) => x.side === s0 || x.side === s1).sort((u, v) => at(u, s0) - at(v, s0))) {
      const o = OPP[t.side], want = at(t, s0) - ext(t, s0) / 2;
      if (want < end[t.side] + G && want >= end[o] + G && t.gaps[o] <= t.gaps[t.side] + W * 0.5) t.side = o;
      end[t.side] = Math.max(end[t.side], want + ext(t, s0));
    }
  }
  const boxHit = (u, v) => u.x < v.x + v.width && v.x < u.x + u.width && u.y < v.y + v.height && v.y < u.y + u.height;
  const holds = (u, v) => { const cx = v.x + v.width / 2, cy = v.y + v.height / 2; return cx > u.x && cx < u.x + u.width && cy > u.y && cy < u.y + u.height; };
  for (const t of tags) {
    const bx = t.gr.box;
    const others = groupsIn.filter((o) => o !== t.gr).map((o) => o.box);
    const edge = [[t.cx, bx.y + bx.height], [bx.x + bx.width, t.cy], [t.cx, bx.y], [bx.x, t.cy]][t.side];
    const inward = [[0, -1], [-1, 0], [0, 1], [1, 0]][t.side];
    if (others.some((o) => holds(bx, o))) {
      const d = Math.min(bx.width, bx.height) * 0.08, len = t.side % 2 === 0 ? bx.width : bx.height;
      const inBox = (x, y) => others.some((o) => x > o.x && x < o.x + o.width && y > o.y && y < o.y + o.height);
      const px = edge[0] + inward[0] * d, py = edge[1] + inward[1] * d;
      const steps = [0, 0.1, -0.1, 0.2, -0.2, 0.3, -0.3, 0.38, -0.38];
      const k = steps.find((f) => !inBox(px + (t.side % 2 === 0 ? f * len : 0), py + (t.side % 2 === 0 ? 0 : f * len))) ?? 0;
      t.ax = px + (t.side % 2 === 0 ? k * len : 0); t.ay = py + (t.side % 2 === 0 ? 0 : k * len);
    } else if (others.some((o) => boxHit(bx, o))) {
      t.ax = t.cx; t.ay = t.cy;
    } else {
      t.ax = edge[0]; t.ay = edge[1];
    }
  }
  for (const side of [0, 1, 2, 3]) {
    const row = side % 2 === 0;
    const list = tags.filter((t) => t.side === side).sort((u, v) => (row ? u.ax - v.ax : u.ay - v.ay));
    const blocks = [];
    for (const t of list) {
      t.ext = row ? t.tw : t.th;
      t.want = (row ? t.ax : t.ay) - t.ext / 2;
      blocks.push({ items: [t], start: t.want, size: t.ext });
      while (blocks.length > 1) {
        const p0 = blocks[blocks.length - 2], p1 = blocks[blocks.length - 1];
        if (p0.start + p0.size + G <= p1.start) break;
        const items = p0.items.concat(p1.items);
        let acc = 0, sum = 0;
        for (const it of items) { sum += it.want - acc; acc += it.ext + G; }
        blocks.splice(blocks.length - 2, 2, { items, start: sum / items.length, size: acc - G });
      }
    }
    for (const bl of blocks) {
      let acc = bl.start;
      for (const t of bl.items) {
        if (row) { t.x = acc; t.y = side === 0 ? U.y1 + off : U.y0 - off - t.th; }
        else { t.y = acc; t.x = side === 1 ? U.x1 + off : U.x0 - off - t.tw; }
        acc += t.ext + G;
      }
    }
  }
  tags.forEach((t, k) => {
    const g = -2 - k, ax = t.ax, ay = t.ay;
    const rt = Math.min(R, t.tw / 2, t.th / 2) + hair;
    const clampX = (v) => (t.tw > 2 * rt ? Math.min(Math.max(v, t.x + rt), t.x + t.tw - rt) : t.x + t.tw / 2);
    const clampY = (v) => (t.th > 2 * rt ? Math.min(Math.max(v, t.y + rt), t.y + t.th - rt) : t.y + t.th / 2);
    const bxp = t.side === 1 ? t.x : t.side === 3 ? t.x + t.tw : clampX(ax);
    const byp = t.side === 0 ? t.y : t.side === 2 ? t.y + t.th : clampY(ay);
    items.push({ k: 'shape', curve: Curve.createLineXY(ax, ay, bxp, byp), fill: null, stroke: ink.concat(140), weight: hair, g });
    const dot = hair * 3;
    items.push({ k: 'shape', curve: Curve.createEllipse({ x: ax - dot, y: ay - dot, width: dot * 2, height: dot * 2 }), fill: ink.concat(255), g });
    items.push({ k: 'shape', curve: roundRect(t.x, t.y, t.tw, t.th, [R, R, R, R]), fill: look.card || (look.border ? null : [255, 255, 255, 235]), stroke: look.border, weight: hair, g });
    let y = t.y + pad;
    if (t.name) {
      items.push({ k: 'text', spec: { align: 0, lead: M.lead, lines: [[{ t: t.name, w: FontWeight.Bold, s: M.fsT, c: ink.concat(255) }]] }, x: t.x + pad, y: y + capT, g });
      y += capT + M.gapTitle;
    }
    t.gr.recs.forEach((i) => {
      items.push({ k: 'shape', curve: roundRect(t.x + pad, y, S, S, [S * 0.18, S * 0.18, S * 0.18, S * 0.18]), fill: recs[i].colour, g });
      if (nLines) {
        const bl = blockSpec(lines[i], M, { text: ink });
        const tx = t.x + pad + S + M.fsC * 0.9, base = y + capC;
        items.push({ k: 'text', spec: bl.labels, x: tx, y: base, g });
        items.push({ k: 'text', spec: bl.values, x: tx + labelsW + colGap, y: base, g });
      }
      y += entryH + G;
    });
  });
  return items;
}

function dialogLang() {
  const offered = ['de', 'en', 'es', 'fr', 'id', 'it', 'ja', 'pt', 'tr', 'zh'];
  const iso = (id) => String(id || '').toLowerCase().slice(0, 2);
  try {
    const { Locale } = require('/locale.js');
    try {
      for (const id of Locale.userPreferredLanguageIDs) {
        if (offered.includes(iso(id))) break;
        if (STRINGS[iso(id)]) return iso(id);
      }
    } catch (e) { }
    const ui = iso(Locale.current.isoCode);
    if (STRINGS[ui]) return ui;
  } catch (e) { }
  return LANG;
}

const UI_LANG = dialogLang();
const T = Object.assign({}, STRINGS.en, STRINGS[UI_LANG] || {});

const hexColour = (h) => [1, 3, 5, 7].map((i) => (i < h.length ? parseInt(h.slice(i, i + 2), 16) : 255));
const pickerColour = (h) => (h.length > 7 && h.slice(7) === '00' ? null : rgba(hexColour(h)));
const fromPicker = (col) => {
  if (!col) return null;
  const c = col.rgba8;
  return c.alpha === 0 ? null : [c.r, c.g, c.b, c.alpha];
};

const doc = Document.current;
if (!doc) {
  app.alert(T.noDoc, NAME);
} else if (!doc.selection.firstNode) {
  app.alert(T.noSel, NAME);
} else {
  const sel = [...doc.selection.nodes];
  const isNative = nativeTester();

  const readCache = {};
  const readAll = (p) => {
    const key = `${p.strokes}|${p.gradients}|${!!p.images}|${p.imageQuality || 0}|${normalizeMaxColours(p.maxColours)}`;
    if (readCache[key]) return readCache[key];
    const { found, texts } = collectColours(sel, GROUP, p);
    for (const t of texts) found.push(...textColours(doc, t, GROUP, p));
    return (readCache[key] = uniqueColours(found, isNative));
  };

  const first = readAll(DEFAULTS);
  if (!first.length && !readAll(Object.assign({}, DEFAULTS, { strokes: true, gradients: true })).length) {
    app.alert(T.noColours, NAME);
  } else {
    const boxes = sel.map((n) => { try { return n.spreadBaseBox; } catch (e) { return null; } });
    const U = boxes.filter(Boolean).reduce((a, b) => {
      if (!a) return { x: b.x, y: b.y, x1: b.x + b.width, y1: b.y + b.height };
      return { x: Math.min(a.x, b.x), y: Math.min(a.y, b.y), x1: Math.max(a.x1, b.x + b.width), y1: Math.max(a.y1, b.y + b.height) };
    }, null) || { x: 0, y: 0, x1: 0, y1: 0 };

    const node = sel[0];
    const placeAbove = (nd) => {
      const above = nd.nextSibling;
      return above ? [above, InsertionMode.Behind] : [nd.parent, InsertionMode.Inside_AtBack];
    };
    const inside = node.isArtboardEnabled === true ? null : sel.length > 1 ? [node.parent, InsertionMode.Inside_AtBack] : placeAbove(node);
    let artboard = null;
    for (let a = node.isArtboardEnabled === true ? node : node.parent; a; a = a.parent) {
      if (a.isArtboardEnabled === true) { artboard = a; break; }
    }
    const outside = artboard ? placeAbove(artboard) : inside;
    const artBox = artboard ? artboard.spreadBaseBox : null;

    const profiles = ColourProfile.getProfilesForColourSpace(ColourSpaceType.CMYK);
    const docProfile = doc.colourProfile;
    const defaultProfile = docProfile && docProfile.colourSpace === ColourSpaceType.CMYK ? docProfile : ColourProfile.getDefaultForColourSpace(ColourSpaceType.CMYK);
    const profileIndex0 = Math.max(0, profiles.findIndex((pr) => pr.name === defaultProfile.name));
    const profileSets = profiles.map(() => null);
    const profileSet = (i) => {
      if (!profileSets[i]) {
        const s = ColourProfileSet.create();
        s.setProfileForColourSpaceType(ColourSpaceType.CMYK, profiles[i]);
        profileSets[i] = s;
      }
      return profileSets[i];
    };

    const kdpi = doc.dpi / 72;
    const W0 = Math.round(Math.min(240 * kdpi, Math.max(100 * kdpi, (U.x1 - U.x) / 4)));

    const { Font, FontFamily } = require('/fonts.js');
    const familyNames = new Set([...FontFamily.all].map((f) => f.name));
    const prefs = (UI_LANG === 'ja' ? ['Hiragino Sans', 'Yu Gothic UI', 'Yu Gothic', 'Noto Sans JP', 'Meiryo'] : []).concat(['Inter', 'Helvetica Neue', 'SF Pro Text', 'Segoe UI']);
    const font0 = prefs.find((f) => familyNames.has(f)) || Font.createDefault().familyName;

    const COL_WIDTHS = [1, 0.62, 1.12];
    const dlg = Dialog.create(`${NAME} ${VERSION} — Visual.af`);
    const main = dlg.addColumn();
    const topStack = main.addGroup('').addColumnStack();
    const top = COL_WIDTHS.map((w) => topStack.addColumn().setWidthProportion(w));
    const layoutBox = top[0].addGroup('').addComboBox(T.layout, T.layoutOptions, 0);
    const styleBox = top[1].addGroup('').addComboBox(T.style, T.styleOptions, 0);
    const sizeBox = top[2].addGroup('')
      .addUnitValueEditor(T.size, UnitType.Pixel, doc.units, W0, 4, 20000).setShowPopupSlider(true).setPrecision(1);
    sizeBox.setDescription(T.sizeHint);

    const midStack = main.addGroup('').setEnableSeparator(true).addColumnStack();
    const cols = COL_WIDTHS.map((w) => midStack.addColumn().setWidthProportion(w));
    dlg.initialWidth = 800;
    dlg.isResizable = true;

    const P0 = Object.assign({}, DEFAULTS, STYLES[0].params, { profile: profileIndex0 });
    const groups = {}, ctrls = {};
    for (const c of CONTROLS) {
      if (!groups[c.group]) groups[c.group] = cols[c.column].addGroup(T[c.group]).setEnableSeparator(true);
      const g = groups[c.group], label = T[c.key], v = P0[c.key];
      let ctl;
      if (c.kind === 'range') {
        const unit = c.unit === '%' ? UnitType.Percentage : UnitType.Number;
        ctl = g.addUnitValueEditor(label, unit, unit, v, c.min, c.max).setShowPopupSlider(true).setPrecision(c.decimals);
      } else if (c.kind === 'select') {
        ctl = g.addComboBox(label, T[c.key + 'Options'], v);
      } else if (c.kind === 'profile') {
        ctl = g.addComboBox(label, profiles.map((pr) => pr.name), v);
      } else if (c.kind === 'switch') {
        ctl = g.addSwitch(label, v);
      } else if (c.kind === 'font') {
        ctl = g.addFontPicker(label);
        ctl.text = font0;
      } else {
        ctl = g.addColourPicker(label, pickerColour(v));
        if (c.none) ctl.setAllowPickNone(true);
      }
      if (T[c.key + 'Hint']) ctl.setDescription(T[c.key + 'Hint']);
      ctrls[c.key] = ctl;
    }

    const foot = main.addGroup('').setEnableSeparator(true);
    const stats = foot.addStaticText('', '').setIsFullWidth(true);
    foot.addStaticText('', T.credit).setIsFullWidth(true);

    const readParams = () => {
      const p = { layout: layoutBox.selectedIndex, size: Number(sizeBox.value) };
      for (const c of CONTROLS) {
        const ctl = ctrls[c.key];
        p[c.key] = c.kind === 'range' ? Number(ctl.value)
          : c.kind === 'select' || c.kind === 'profile' ? ctl.selectedIndex
          : c.kind === 'switch' ? !!ctl.value
          : c.kind === 'font' ? ((ctl.fontFamily && ctl.fontFamily.name) || ctl.text || font0)
          : fromPicker(ctl.value);
      }
      return p;
    };

    const refreshEnabled = (p) => {
      for (const c of CONTROLS) if (c.on) ctrls[c.key].isEnabled = !!p[c.on];
      ctrls.profile.isEnabled = p.cmyk || p.cmykEd;
      ctrls.imageQuality.isEnabled = !!p.images;
      const tags = LAYOUTS[p.layout].key === 'tags';
      ctrls.perRow.isEnabled = !tags;
      ctrls.tints.isEnabled = !tags;
    };

    const widths = new Map();
    let capRatio = 0.716;
    let measuredFont = null;
    const measureAll = (font, strings, target, mode) => {
      if (measuredFont !== font) { widths.clear(); measuredFont = font; capRatio = 0; }
      const todo = [];
      const want = (w, tr, t) => {
        const key = measureKey(font, w, tr, t);
        if (!widths.has(key) && !todo.some((x) => x.key === key)) todo.push({ key, w, tr, t });
      };
      if (!capRatio) want(FontWeight.Medium, 0, 'H');
      for (const s of strings) want(s[0], s[1], s[2]);
      if (!todo.length) return;
      const b = AddChildNodesCommandBuilder.create();
      todo.forEach((x, i) => {
        const d = textDef(doc, font, { align: 0, lead: REF * 1.5, lines: [[{ t: x.t, w: x.w, s: REF, tr: x.tr, c: [0, 0, 0, 255] }]] }, 0, 0);
        d.userDescription = 'm' + i;
        b.addNode(d);
      });
      b.setInsertionTarget(target);
      b.setInsertionMode(mode);
      const cmd = b.createCommand(false, NodeChildType.Main);
      doc.executeCommand(cmd, true);
      for (const nd of cmd.newNodes) {
        const x = todo[Number(String(nd.userDescription).slice(1))];
        if (!x) continue;
        const box = nd.spreadBaseBox;
        widths.set(x.key, box.width / REF);
        if (x.t === 'H' && x.w === FontWeight.Medium && !x.tr) capRatio = -box.y / REF;
      }
      if (!capRatio) capRatio = 0.716;
    };

    const compute = (p, target, mode) => {
      const set = profileSet(p.profile);
      let recs = readAll(p).map((r) => Object.assign({}, r));
      for (const r of recs) derive(r, set);
      const total = recs.length;
      recs = mergeSimilar(recs, p.merge / 100);
      const merged = total - recs.length;
      const hasRaster = recs.some((r) => r.srcs.some((src) => src.kind === 'raster'));
      const maxColours = normalizeMaxColours(p.maxColours);
      const capped = recs.length > maxColours;
      if (capped && hasRaster) {
        recs = recs.slice().sort((a, b) => b.count - a.count || a.index - b.index).slice(0, maxColours);
      }
      recs = orderColours(recs, p.order);
      if (capped && !hasRaster) recs = recs.slice(0, maxColours);

      const lines = recs.map((r) => codeLines(r, p, T));
      const titles = recs.map((r, i) => {
        if (p.title === 2) return '';
        const num = `${T.colourWord} ${String(i + 1).padStart(2, '0')}`;
        if (p.title === 1) return num;
        const s = r.srcs.find((x) => x.name);
        if (!s) return num;
        return s.kind === 'stroke' && !r.srcs.some((x) => x.name === s.name && x.kind !== 'stroke') ? `${s.name} · ${T.strokeWord}` : s.name;
      });

      const tagGroups = [];
      if (LAYOUTS[p.layout].key === 'tags') {
        sel.forEach((nd, top) => {
          if (!boxes[top]) return;
          const idx = recs.map((r, i) => (r.srcs.some((s) => s.top === top) ? i : -1)).filter((i) => i >= 0);
          if (idx.length) tagGroups.push({ box: boxes[top], recs: idx, title: p.title === 0 ? nd.userDescription || '' : '' });
        });
      }

      const strings = [];
      for (const t of titles) if (t) strings.push([FontWeight.Bold, 0, t]);
      for (const g of tagGroups) if (g.title) strings.push([FontWeight.Bold, 0, g.title]);
      for (const ls of lines) for (const l of ls) { strings.push([FontWeight.Normal, 0, l[0]]); strings.push([FontWeight.Medium, 0, l[1]]); }
      measureAll(p.font, strings, target, mode);
      const mw = (w, tr, t) => widths.get(measureKey(p.font, w, tr, t)) || t.length * 0.6;

      const look = { card: p.card, border: p.border, text: (p.text || [17, 17, 17]).slice(0, 3) };
      let items, box;
      if (LAYOUTS[p.layout].key === 'tags') {
        items = layoutTags(tagGroups, recs, lines, titles, p, p.size, look, mw, capRatio);
        box = null;
      } else {
        const L = layoutPalette(recs, lines, titles, p, p.size, look, mw, capRatio);
        const off = p.size * 0.3;
        const ox = p.position === 1 ? U.x1 + off : p.position === 3 ? U.x - off - L.w : U.x;
        const oy = p.position === 0 ? U.y1 + off : p.position === 2 ? U.y - off - L.h : U.y;
        items = L.items.map((it) => Object.assign({}, it, { dx: ox, dy: oy }));
        box = { x: ox, y: oy, x1: ox + L.w, y1: oy + L.h };
      }
      const hexOf = (r) => '#' + r.rgb.map(hex2).join('');
      const names = new Map();
      recs.forEach((r, i) => names.set(i, hexOf(r)));
      tagGroups.forEach((g, k) => names.set(-2 - k, g.title || g.recs.map((i) => hexOf(recs[i])).join(' ')));
      return { recs, items, box, total, merged, capped, maxColours, names };
    };

    const toDef = (it) => {
      const dx = it.dx || 0, dy = it.dy || 0;
      if (it.k === 'text') return textDef(doc, lastParams.font, it.spec, it.x + dx, it.y + dy);
      const pc = PolyCurve.create();
      pc.addCurve(it.curve);
      if (dx || dy) pc.transform(Transform.createTranslate(dx, dy));
      const fill = !it.fill ? FillDescriptor.createNone() : FillDescriptor.createSolid(Array.isArray(it.fill) ? rgba(it.fill) : it.fill);
      const stroke = it.stroke ? FillDescriptor.createSolid(rgba(it.stroke)) : FillDescriptor.createNone();
      const ls = LineStyleDescriptor.create(LineStyle.create({ weight: it.stroke ? it.weight : 1, cap: LineCap.Round, join: LineJoin.Round }));
      return PolyCurveNodeDefinition.create(pc, fill, stroke, ls, FillDescriptor.createNone());
    };

    const count = (n) => (n === 1 ? T.stats.one : T.stats.many.replace('{n}', n));
    const showStats = (r) => {
      const parts = [count(r.total)];
      if (r.merged) parts.push(T.stats.merged.replace('{n}', r.merged));
      if (r.capped) parts.push(T.stats.capped.replace('{n}', r.maxColours));
      stats.text = parts.join('  ·  ');
    };

    const where = (box) => {
      if (!artBox || !box) return inside || outside;
      const fits = box.x >= artBox.x && box.y >= artBox.y && box.x1 <= artBox.x + artBox.width && box.y1 <= artBox.y + artBox.height;
      return fits && inside ? inside : outside;
    };

    let lastParams = null;
    const update = (preview) => {
      const p = readParams();
      lastParams = p;
      refreshEnabled(p);
      const [mt, mm] = inside || outside;
      const r = compute(p, mt, mm);
      showStats(r);
      const [target, mode] = where(r.box);
      const defs = r.items.map(toDef);
      if (preview) {
        if (!defs.length) { doc.clearPreviews(); return; }
        const b = AddChildNodesCommandBuilder.create();
        for (const d of mode === InsertionMode.Behind ? defs.slice().reverse() : defs) b.addNode(d);
        b.setInsertionTarget(target);
        b.setInsertionMode(mode);
        doc.executeCommand(b.createCommand(false, NodeChildType.Main), true);
        return;
      }
      doc.clearPreviews();
      if (!defs.length) return;
      const bg = AddChildNodesCommandBuilder.create();
      bg.addContainerNode(ContainerNodeDefinition.create(GROUP));
      bg.setInsertionTarget(target);
      bg.setInsertionMode(mode);
      const cmd = bg.createCommand(true, NodeChildType.Main);
      doc.executeCommand(cmd);
      const group = [...cmd.newNodes][0];

      const byGroup = new Map();
      r.items.forEach((it, i) => {
        if (!byGroup.has(it.g)) byGroup.set(it.g, []);
        byGroup.get(it.g).push(defs[i]);
      });
      const keys = [...byGroup.keys()].filter((g) => g !== -1).sort((x, y) => (x >= 0 ? x - y : y - x));
      const used = new Set();
      const names = keys.map((g) => {
        const base = r.names.get(g);
        let name = base, k = 2;
        while (used.has(name)) name = `${base} (${k++})`;
        used.add(name);
        return name;
      });
      const b2 = AddChildNodesCommandBuilder.create();
      for (const d of byGroup.get(-1) || []) b2.addNode(d);
      for (const nm of names) b2.addContainerNode(ContainerNodeDefinition.create(nm));
      b2.setInsertionTarget(group);
      b2.setInsertionMode(InsertionMode.Inside_AtBack);
      const cmd2 = b2.createCommand(false, NodeChildType.Main);
      doc.executeCommand(cmd2);
      const containers = new Map();
      for (const nd of cmd2.newNodes) if (nd.isContainerNode) containers.set(String(nd.userDescription), nd);

      const cb = CompoundCommandBuilder.create();
      keys.forEach((g, i) => {
        const c = containers.get(names[i]);
        if (!c) return;
        const b3 = AddChildNodesCommandBuilder.create();
        for (const d of byGroup.get(g)) b3.addNode(d);
        b3.setInsertionTarget(c);
        b3.setInsertionMode(InsertionMode.Inside_AtBack);
        cb.addCommand(b3.createCommand(false, NodeChildType.Main), i === 0);
      });
      doc.executeCommand(cb.createCommand());
    };

    let lastLayout = 0, lastStyle = 0, applying = false;
    dlg.onControlValueChangedHandler = () => {
      if (applying) return;
      const li = layoutBox.selectedIndex, si = styleBox.selectedIndex;
      if (li !== lastLayout || si !== lastStyle) {
        applying = true;
        try {
          if (li !== lastLayout) {
            ctrls.spacing.value = LAYOUTS[li].spacing;
            ctrls.radius.value = LAYOUTS[li].radius;
          }
          if (si !== lastStyle) {
            for (const c of CONTROLS) if (c.look) ctrls[c.key].value = pickerColour(STYLES[si].params[c.key]);
          }
        } finally {
          applying = false;
        }
        lastLayout = li;
        lastStyle = si;
      }
      update(true);
    };

    update(true);
    if (dlg.runModal() == DialogResult.Ok) {
      update(false);
    } else {
      doc.clearPreviews();
    }
  }
}