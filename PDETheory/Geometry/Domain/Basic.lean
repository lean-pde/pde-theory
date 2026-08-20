import PDETheory.Geometry.Domain.Projection

/-!
# Domains with a locally graphical boundary

This file introduces `PDETheory.HasBoundaryGraphOf`, the geometric core shared by every notion of
boundary regularity in this development: a set `Ω` whose boundary is, near each of its points and
after choosing a local vertical direction `ν`, the graph of a function `φ` in a prescribed
regularity class `P`, with `Ω` lying (locally) strictly on the `+ν` side of that graph.

The definition carries two design commitments:

* the local description is a **set equation** `Ω ∩ C = strictEpigraph … ∩ C` inside a coordinate
  cylinder `C`, not merely `frontier Ω ∩ C = graph`; this pins down which side is `Ω` and excludes
  slit / two-sided boundaries;
* a **`graph_fits`** hypothesis forces the graph to stay inside the cylinder, so the set equation
  is not vacuous near the top/bottom caps.

Concrete regularity classes (`IsLipschitzDomain`, `IsC1Domain`, `IsSmoothDomain`, …) are obtained
by instantiating `P`.

## Main results

* `PDETheory.frontier_inter_eq_of_isOpen` : frontier is local on open sets — a general-topology
  helper of independent interest.
* `PDETheory.HasBoundaryGraphOf.mono_pred` : monotonicity in the regularity predicate.
* `PDETheory.HasBoundaryGraphOf.frontier_eq_graph_locally` : the headline fact that `∂Ω` is, in
  each boundary chart, exactly the graph.
-/

open scoped RealInnerProductSpace
open Set

namespace PDETheory

/-! ### Frontier is local on open sets

These three lemmas are pure general topology: on an open set `U`, the closure, interior, and hence
frontier of a set are determined by the set's trace on `U`. -/

section Topology

variable {X : Type*} [TopologicalSpace X]

lemma closure_inter_eq_of_isOpen {A B U : Set X} (hU : IsOpen U) (hAB : A ∩ U = B ∩ U) :
    closure A ∩ U = closure B ∩ U := by
  have key : ∀ S : Set X, closure S ∩ U = closure (S ∩ U) ∩ U := by
    intro S
    refine subset_antisymm (fun x hx => ⟨?_, hx.2⟩)
      (fun x hx => ⟨closure_mono inter_subset_left hx.1, hx.2⟩)
    have hmem : x ∈ U ∩ closure S := ⟨hx.2, hx.1⟩
    have hx' := hU.inter_closure hmem
    rwa [inter_comm] at hx'
  rw [key A, hAB, ← key B]

lemma interior_inter_eq_of_isOpen {A B U : Set X} (hU : IsOpen U) (hAB : A ∩ U = B ∩ U) :
    interior A ∩ U = interior B ∩ U := by
  have key : ∀ S : Set X, interior S ∩ U = interior (S ∩ U) := by
    intro S; rw [interior_inter, hU.interior_eq]
  rw [key A, hAB, ← key B]

/-- On an open set `U`, the frontier of a set is determined by its trace on `U`. -/
lemma frontier_inter_eq_of_isOpen {A B U : Set X} (hU : IsOpen U) (hAB : A ∩ U = B ∩ U) :
    frontier A ∩ U = frontier B ∩ U := by
  have hc := closure_inter_eq_of_isOpen hU hAB
  have hi := interior_inter_eq_of_isOpen hU hAB
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    refine ⟨⟨?_, ?_⟩, hxU⟩
    · have hmem : x ∈ closure A ∩ U := ⟨hx.1, hxU⟩
      rw [hc] at hmem; exact hmem.1
    · intro hB
      have hmem : x ∈ interior B ∩ U := ⟨hB, hxU⟩
      rw [← hi] at hmem; exact hx.2 hmem.1
  · rintro ⟨hx, hxU⟩
    refine ⟨⟨?_, ?_⟩, hxU⟩
    · have hmem : x ∈ closure B ∩ U := ⟨hx.1, hxU⟩
      rw [← hc] at hmem; exact hmem.1
    · intro hA
      have hmem : x ∈ interior A ∩ U := ⟨hA, hxU⟩
      rw [hi] at hmem; exact hx.2 hmem.1

end Topology

/-! ### The boundary-graph predicate -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Ω` has a boundary that is, near each boundary point, the graph of a `P`-regular function.

Explicitly: for every `z ∈ frontier Ω` there is a unit direction `ν`, a graph function `φ` with
`P φ`, and a coordinate cylinder of radius `r` and half-height `h` about `z`, such that inside the
cylinder `Ω` coincides with the strict epigraph of `φ`. The `graph_fits` clause
`∀ y, ⟪y, ν⟫ = 0 → ‖y‖ < r → |φ y| < h` keeps the graph inside the cylinder. -/
def HasBoundaryGraphOf (P : (E → ℝ) → Prop) (Ω : Set E) : Prop :=
  ∀ z ∈ frontier Ω, ∃ (ν : E) (φ : E → ℝ) (r h : ℝ),
    ‖ν‖ = 1 ∧ 0 < r ∧ 0 < h ∧ P φ ∧
    (∀ y, ⟪y, ν⟫ = 0 → ‖y‖ < r → |φ y| < h) ∧
    Ω ∩ cylinder z ν r h = strictEpigraph z ν φ ∩ cylinder z ν r h

variable {P Q : (E → ℝ) → Prop} {Ω : Set E}

/-- Weakening the regularity class weakens the boundary-graph condition. -/
lemma HasBoundaryGraphOf.mono_pred (hPQ : ∀ φ, P φ → Q φ) (h : HasBoundaryGraphOf P Ω) :
    HasBoundaryGraphOf Q Ω := by
  intro z hz
  obtain ⟨ν, φ, r, hgt, hν, hr, hh, hP, hfit, heq⟩ := h z hz
  exact ⟨ν, φ, r, hgt, hν, hr, hh, hPQ φ hP, hfit, heq⟩

/-- **The boundary is locally a graph.** If `Ω` has a `P`-regular boundary graph and every
`P`-function is continuous, then at each boundary point there is a chart in which `frontier Ω`
coincides with the graph of `φ`. -/
lemma HasBoundaryGraphOf.frontier_eq_graph_locally (hP : ∀ φ, P φ → Continuous φ)
    (h : HasBoundaryGraphOf P Ω) {z : E} (hz : z ∈ frontier Ω) :
    ∃ (ν : E) (φ : E → ℝ) (r hgt : ℝ),
      ‖ν‖ = 1 ∧ 0 < r ∧ 0 < hgt ∧ Continuous φ ∧
      frontier Ω ∩ cylinder z ν r hgt = graphSet z ν φ ∩ cylinder z ν r hgt := by
  obtain ⟨ν, φ, r, hgt, hν, hr, hh, hPφ, _hfit, heq⟩ := h z hz
  refine ⟨ν, φ, r, hgt, hν, hr, hh, hP φ hPφ, ?_⟩
  rw [frontier_inter_eq_of_isOpen (isOpen_cylinder z ν r hgt) heq,
    frontier_strictEpigraph (hP φ hPφ) hν z]

end PDETheory
