import PDETheory.Geometry.Domain.Projection
import PDETheory.Geometry.Domain.Basic
import PDETheory.Geometry.Domain.Lipschitz
import PDETheory.Geometry.Domain.Smooth
import PDETheory.Geometry.Domain.Bounded
import PDETheory.Geometry.Domain.SurfaceMeasure
import PDETheory.Geometry.Domain.Examples

/-!
# Domains and boundary regularity

This is the aggregator module for the theory of domains with regular boundary. It re-exports:

* `PDETheory.Geometry.Domain.Projection` — the coordinate-free local primitives (`baseProj`,
  `cylinder`, `strictEpigraph`, `graphSet`) and their basic analysis.
* `PDETheory.Geometry.Domain.Basic` — the boundary-graph core `HasBoundaryGraphOf`, frontier
  locality on open sets, and the "boundary is locally a graph" result.
* `PDETheory.Geometry.Domain.Lipschitz` — `HasLipschitzBoundary(With)`, `IsLipschitzDomain`,
  `IsSpecialLipschitzDomain`, and that a special Lipschitz domain is a Lipschitz domain.
* `PDETheory.Geometry.Domain.Smooth` — the `Cᵏ` ladder: `IsCkDomain`, `IsC1Domain`,
  `IsSmoothDomain`, `IsAnalyticDomain`.
* `PDETheory.Geometry.Domain.Bounded` — `IsBoundedLipschitzDomain`, the finite `LipschitzAtlas`
  (Lipschitz character), and its existence via compactness of the boundary.
* `PDETheory.Geometry.Domain.SurfaceMeasure` — the graph parametrisation and its `√(1+K²)`-Lipschitz
  bound, the Hausdorff-measure bound on the boundary graph, and the surface measure.
* `PDETheory.Geometry.Domain.Examples` — the half-space as a worked example.
-/
