import PDETheory.Geometry.Domain.Lipschitz

/-!
# Bounded Lipschitz domains and the Lipschitz atlas

A **bounded Lipschitz domain** is a Lipschitz domain with bounded underlying set — the setting of
Dahlberg's theorem and Shen's Stokes estimates. In finite dimensions its boundary is compact, which
upgrades the pointwise boundary charts to a **finite** atlas with a uniform Lipschitz constant and a
uniform positive radius (the quantitative "Lipschitz character" that harmonic-analysis constants
depend on).

## Main definitions / results

* `PDETheory.IsBoundedLipschitzDomain`.
* `PDETheory.isCompact_frontier_of_isBounded` : in finite dimensions the frontier of a bounded set
  is compact.
* `PDETheory.LipschitzAtlas` : a finite boundary atlas with uniform constant and radius.
* `PDETheory.IsBoundedLipschitzDomain.nonempty_lipschitzAtlas` : every bounded Lipschitz domain (in
  finite dimensions) admits such an atlas.
-/

open scoped RealInnerProductSpace NNReal
open Set Bornology

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Set E}

/-- A bounded Lipschitz domain: a Lipschitz domain whose underlying set is bounded. -/
def IsBoundedLipschitzDomain (Ω : Set E) : Prop :=
  IsLipschitzDomain Ω ∧ IsBounded Ω

lemma IsBoundedLipschitzDomain.isLipschitzDomain (h : IsBoundedLipschitzDomain Ω) :
    IsLipschitzDomain Ω := h.1

lemma IsBoundedLipschitzDomain.isBounded (h : IsBoundedLipschitzDomain Ω) : IsBounded Ω := h.2

lemma IsBoundedLipschitzDomain.isOpen (h : IsBoundedLipschitzDomain Ω) : IsOpen Ω := h.1.1

/-- In finite dimensions, the frontier of a bounded set is compact. -/
lemma isCompact_frontier_of_isBounded [FiniteDimensional ℝ E] (hb : IsBounded Ω) :
    IsCompact (frontier Ω) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  exact Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

lemma IsBoundedLipschitzDomain.isCompact_frontier [FiniteDimensional ℝ E]
    (h : IsBoundedLipschitzDomain Ω) : IsCompact (frontier Ω) :=
  isCompact_frontier_of_isBounded h.isBounded

/-- A point lies in the coordinate cylinder centred at itself. -/
lemma self_mem_cylinder {z ν : E} {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    z ∈ cylinder z ν r h := by
  have h0 : baseProj ν (0 : E) = 0 := by simp [baseProj]
  simp only [cylinder, mem_ofPred_eq, sub_self, inner_zero_left, abs_zero, h0]
  exact ⟨by simpa using hr, hh⟩

/-! ### The Lipschitz atlas -/

/-- A single boundary chart: a centre on `∂Ω`, a unit direction, a graph function, and the radius
and half-height of its coordinate cylinder. -/
structure BoundaryChart (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The centre of the chart (a boundary point). -/
  center : E
  /-- The chart's vertical direction (a unit vector; not the geometric normal). -/
  normal : E
  /-- The graph function. -/
  graph : E → ℝ
  /-- The base radius of the coordinate cylinder. -/
  radius : ℝ
  /-- The half-height of the coordinate cylinder. -/
  depth : ℝ

/-- A **finite Lipschitz atlas** for `Ω`: finitely many boundary charts sharing a uniform Lipschitz
constant `const` and a uniform positive radius `minRadius`, whose cylinders cover `frontier Ω` and
each of which realises `Ω` locally as a strict epigraph. This is the quantitative "Lipschitz
character" of the domain. -/
structure LipschitzAtlas (Ω : Set E) where
  /-- The (finite) set of charts. -/
  charts : Set (BoundaryChart E)
  /-- Finiteness of the atlas. -/
  charts_finite : charts.Finite
  /-- The uniform Lipschitz constant. -/
  const : ℝ≥0
  /-- The uniform lower bound on chart radii. -/
  minRadius : ℝ
  minRadius_pos : 0 < minRadius
  normal_unit : ∀ c ∈ charts, ‖c.normal‖ = 1
  graph_lipschitz : ∀ c ∈ charts, LipschitzWith const c.graph
  radius_ge : ∀ c ∈ charts, minRadius ≤ c.radius
  depth_pos : ∀ c ∈ charts, 0 < c.depth
  center_mem : ∀ c ∈ charts, c.center ∈ frontier Ω
  graph_fits : ∀ c ∈ charts, ∀ y, ⟪y, c.normal⟫ = 0 → ‖y‖ < c.radius → |c.graph y| < c.depth
  epigraph : ∀ c ∈ charts,
    Ω ∩ cylinder c.center c.normal c.radius c.depth
      = strictEpigraph c.center c.normal c.graph ∩ cylinder c.center c.normal c.radius c.depth
  covers : ∀ z ∈ frontier Ω, ∃ c ∈ charts, z ∈ cylinder c.center c.normal c.radius c.depth

/-- **Every bounded Lipschitz domain (in finite dimensions) admits a finite Lipschitz atlas.**
The uniform Lipschitz constant is supplied by the definition of `HasLipschitzBoundary`; compactness
of the boundary supplies the finite chart set and the uniform positive radius. -/
theorem IsBoundedLipschitzDomain.nonempty_lipschitzAtlas [FiniteDimensional ℝ E]
    (h : IsBoundedLipschitzDomain Ω) : Nonempty (LipschitzAtlas Ω) := by
  obtain ⟨M, hM⟩ := h.isLipschitzDomain.2
  -- Choose chart data at every boundary point.
  have key : ∀ z : frontier Ω, ∃ (ν : E) (φ : E → ℝ) (r d : ℝ),
      ‖ν‖ = 1 ∧ 0 < r ∧ 0 < d ∧ LipschitzWith M φ ∧
      (∀ y, ⟪y, ν⟫ = 0 → ‖y‖ < r → |φ y| < d) ∧
      Ω ∩ cylinder z.1 ν r d = strictEpigraph z.1 ν φ ∩ cylinder z.1 ν r d :=
    fun z => hM z.1 z.2
  choose ν φ rad dep hunit hrpos hdpos hlip hfits hepi using key
  set U : frontier Ω → Set E := fun z => cylinder z.1 (ν z) (rad z) (dep z) with hU
  have hUo : ∀ z, IsOpen (U z) := fun z => isOpen_cylinder _ _ _ _
  have hcov : frontier Ω ⊆ ⋃ z, U z := fun w hw =>
    Set.mem_iUnion.mpr ⟨⟨w, hw⟩, self_mem_cylinder (hrpos _) (hdpos _)⟩
  obtain ⟨t, ht⟩ := h.isCompact_frontier.elim_finite_subcover U hUo hcov
  set chartOf : frontier Ω → BoundaryChart E :=
    fun z => ⟨z.1, ν z, φ z, rad z, dep z⟩ with hchart
  rcases t.eq_empty_or_nonempty with rfl | hne
  · -- Empty subcover: the boundary is empty, so the empty atlas works.
    have hfe : frontier Ω = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    exact ⟨{
      charts := ∅
      charts_finite := Set.finite_empty
      const := M
      minRadius := 1
      minRadius_pos := one_pos
      normal_unit := fun c hc => absurd hc (Set.notMem_empty c)
      graph_lipschitz := fun c hc => absurd hc (Set.notMem_empty c)
      radius_ge := fun c hc => absurd hc (Set.notMem_empty c)
      depth_pos := fun c hc => absurd hc (Set.notMem_empty c)
      center_mem := fun c hc => absurd hc (Set.notMem_empty c)
      graph_fits := fun c hc => absurd hc (Set.notMem_empty c)
      epigraph := fun c hc => absurd hc (Set.notMem_empty c)
      covers := fun z hz => absurd (hfe ▸ hz) (Set.notMem_empty z) }⟩
  · exact ⟨{
      charts := chartOf '' ↑t
      charts_finite := t.finite_toSet.image chartOf
      const := M
      minRadius := t.inf' hne rad
      minRadius_pos := (Finset.lt_inf'_iff hne).mpr fun z _ => hrpos z
      normal_unit := Set.forall_mem_image.mpr fun z _ => hunit z
      graph_lipschitz := Set.forall_mem_image.mpr fun z _ => hlip z
      radius_ge := Set.forall_mem_image.mpr fun z hz => Finset.inf'_le rad (Finset.mem_coe.mp hz)
      depth_pos := Set.forall_mem_image.mpr fun z _ => hdpos z
      center_mem := Set.forall_mem_image.mpr fun z _ => z.2
      graph_fits := Set.forall_mem_image.mpr fun z _ => hfits z
      epigraph := Set.forall_mem_image.mpr fun z _ => hepi z
      covers := fun w hw => by
        obtain ⟨i, hit, hwi⟩ := Set.mem_iUnion₂.mp (ht hw)
        exact ⟨chartOf i, Set.mem_image_of_mem chartOf (Finset.mem_coe.mpr hit), hwi⟩ }⟩

end PDETheory
