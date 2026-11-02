# Logo Construction Grid

Script for Affinity Designer that generates construction grids from selected vector artwork.

## Current version

**Anchors & Closed Bézier v2**

The current development focuses on more reliable analysis of native path anchors and closed Bézier contours.

### Geometry analysis

- Topology-aware anchor identification, keeping distinct native vertices separate even when they overlap spatially.
- Correct handling of the closing seam of closed paths, including implicit closing edges.
- Bézier extrema and curve bounds calculated from the actual curve rather than the control-point hull.
- Inflection and stationary-point analysis, including cusp detection inside cubic segments.
- More reliable endpoint tangents when Bézier handles are degenerate.
- Curvature-aware protection of important anchors in automatic display mode.
- Handle-to-anchor association based on path topology rather than nearest-coordinate matching.

### Validation

The source passed a JavaScript syntax check. The geometry work was also checked with a Node-based test harness (30 assertions). The test harness uses stubbed Affinity interfaces, so visual and runtime validation inside Affinity Designer is still required.

## Installation

1. Download `Logo_Construction_Grid_Anchors_ClosedBezier_v2.js` from this repository.
2. Open Affinity Designer.
3. Run the script using the application's supported scripting workflow.

The exact scripting workflow can vary with the Affinity Designer version.

## Notes

This repository contains an experimental script. Make a copy of your document before running scripts that create or modify document objects.
