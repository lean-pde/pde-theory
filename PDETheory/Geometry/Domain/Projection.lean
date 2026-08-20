import Mathlib

/-!
# Local coordinates for boundary graphs

This file sets up the coordinate-free primitives used to describe a domain whose boundary is,
locally, the graph of a function. Working in a real inner product space `E`, we fix a distinguished
*unit direction* `ν` — the local "vertical", i.e. the axis along which the boundary is written as a
graph — and split `E` orthogonally into the hyperplane `ν^⟂` and the line `ℝ ∙ ν`:

`ν` is a **coordinate choice, not the geometric outward normal**. It is a piece of chart data that
exists at *every* boundary point (corners included, where no normal exists), and its definition
uses no differentiability. The genuine outward unit normal to `∂Ω` is a separate, derived object,
defined only `H^{n-1}`-almost-everywhere via Rademacher's theorem (in these coordinates it is
`(-∇φ, 1)/√(1 + |∇φ|²)` at the differentiability points of `φ`); it is developed later and never
enters the definitions here.

* `PDETheory.baseProj ν x = x - ⟪x, ν⟫ • ν` is the orthogonal projection of `x` onto `ν^⟂`
  (an actual orthogonal projection precisely when `‖ν‖ = 1`);
* the *height* of `x` along `ν` is the inner product `⟪x, ν⟫`.

A graph function `φ : E → ℝ` (only its values on `ν^⟂` matter) then determines the
`PDETheory.strictEpigraph` (the region strictly on the `+ν` side of the graph), its
`PDETheory.graphSet`, and a coordinate `PDETheory.cylinder`.

## Main results

* `PDETheory.norm_sq_baseProj` : the Pythagorean identity `‖baseProj ν x‖² = ‖x‖² - ⟪x, ν⟫²`.
* `PDETheory.lipschitzWith_baseProj`, `PDETheory.lipschitzWith_height` : both projections are
  `1`-Lipschitz.
* `PDETheory.isOpen_strictEpigraph`, `PDETheory.isOpen_cylinder` : openness.
* `PDETheory.frontier_strictEpigraph` : for continuous `φ` and a unit normal, the frontier of the
  strict epigraph is exactly the graph.

## Implementation notes

Nothing here fixes an ambient basis or dimension: the unit normal `ν` plays the role of a
"vertical" direction and the base point of a translation, so no rigid motion / rotation is needed.
Finite-dimensionality and completeness are *not* assumed at this stage.
-/

open scoped RealInnerProductSpace NNReal Topology
open Filter Set

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal projection of `x` onto the hyperplane `ν^⟂`; genuinely the orthogonal projection
when `‖ν‖ = 1`. -/
def baseProj (ν x : E) : E := x - ⟪x, ν⟫ • ν

/-- Open coordinate cylinder about `z`: base-radius `< r` in the `ν^⟂` directions and height
`< h` along `ν`. -/
def cylinder (z ν : E) (r h : ℝ) : Set E :=
  {x | ‖baseProj ν (x - z)‖ < r ∧ |⟪x - z, ν⟫| < h}

/-- Strict epigraph based at `z` with unit direction `ν` and graph function `φ`: the region
strictly on the `+ν` side of the graph of `φ`. -/
def strictEpigraph (z ν : E) (φ : E → ℝ) : Set E :=
  {x | φ (baseProj ν (x - z)) < ⟪x - z, ν⟫}

/-- The local graph through `z` with direction `ν`. -/
def graphSet (z ν : E) (φ : E → ℝ) : Set E :=
  {x | φ (baseProj ν (x - z)) = ⟪x - z, ν⟫}

/-! ### Algebra of `baseProj` -/

lemma baseProj_add (ν x y : E) : baseProj ν (x + y) = baseProj ν x + baseProj ν y := by
  simp only [baseProj, inner_add_left, add_smul]; abel

lemma baseProj_sub (ν x y : E) : baseProj ν (x - y) = baseProj ν x - baseProj ν y := by
  simp only [baseProj, inner_sub_left, sub_smul]; abel

lemma baseProj_smul (ν : E) (c : ℝ) (x : E) : baseProj ν (c • x) = c • baseProj ν x := by
  simp only [baseProj, real_inner_smul_left, mul_smul, smul_sub]

/-- The distinguished direction `ν` is annihilated by its own base projection. -/
lemma baseProj_self_eq_zero {ν : E} (hν : ‖ν‖ = 1) : baseProj ν ν = 0 := by
  simp only [baseProj, real_inner_self_eq_norm_sq, hν]; simp

/-- The base projection lands in the hyperplane `ν^⟂`. -/
lemma inner_baseProj_left {ν : E} (x : E) (hν : ‖ν‖ = 1) : ⟪baseProj ν x, ν⟫ = 0 := by
  simp only [baseProj, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hν]
  ring

/-- Pythagorean identity for the orthogonal splitting `x = baseProj ν x + ⟪x, ν⟫ • ν`. -/
lemma norm_sq_baseProj {ν : E} (x : E) (hν : ‖ν‖ = 1) :
    ‖baseProj ν x‖ ^ 2 = ‖x‖ ^ 2 - ⟪x, ν⟫ ^ 2 := by
  have hy : ‖(⟪x, ν⟫ • ν : E)‖ = |⟪x, ν⟫| := by
    rw [norm_smul, Real.norm_eq_abs, hν, mul_one]
  calc ‖baseProj ν x‖ ^ 2
      = ‖x - ⟪x, ν⟫ • ν‖ ^ 2 := rfl
    _ = ‖x‖ ^ 2 - 2 * ⟪x, ⟪x, ν⟫ • ν⟫ + ‖(⟪x, ν⟫ • ν : E)‖ ^ 2 := norm_sub_sq_real _ _
    _ = ‖x‖ ^ 2 - 2 * (⟪x, ν⟫ * ⟪x, ν⟫) + |⟪x, ν⟫| ^ 2 := by
        rw [real_inner_smul_right, hy]
    _ = ‖x‖ ^ 2 - ⟪x, ν⟫ ^ 2 := by rw [sq_abs]; ring

/-! ### Continuity -/

lemma continuous_baseProj (ν : E) : Continuous (baseProj ν) :=
  continuous_id.sub ((continuous_id.inner continuous_const).smul continuous_const)

lemma continuous_height (ν : E) : Continuous fun x : E => ⟪x, ν⟫ :=
  continuous_id.inner continuous_const

/-- The composite `x ↦ φ (baseProj ν (x - z))` used as the "graph side" of the epigraph. -/
lemma continuous_graphComp {φ : E → ℝ} (hφ : Continuous φ) (z ν : E) :
    Continuous fun x : E => φ (baseProj ν (x - z)) :=
  hφ.comp ((continuous_baseProj ν).comp (continuous_id.sub continuous_const))

/-- The composite `x ↦ ⟪x - z, ν⟫` used as the "height side" of the epigraph. -/
lemma continuous_heightComp (z ν : E) : Continuous fun x : E => ⟪x - z, ν⟫ :=
  (continuous_id.sub continuous_const).inner continuous_const

/-! ### Lipschitz bounds -/

lemma lipschitzWith_height {ν : E} (hν : ‖ν‖ = 1) :
    LipschitzWith 1 fun x : E => ⟪x, ν⟫ := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hd : dist (⟪x, ν⟫) (⟪y, ν⟫) = |⟪x - y, ν⟫| := by
    rw [Real.dist_eq, inner_sub_left]
  rw [hd, NNReal.coe_one, one_mul, dist_eq_norm]
  calc |⟪x - y, ν⟫| ≤ ‖x - y‖ * ‖ν‖ := abs_real_inner_le_norm _ _
    _ = ‖x - y‖ := by rw [hν, mul_one]

lemma lipschitzWith_baseProj {ν : E} (hν : ‖ν‖ = 1) :
    LipschitzWith 1 (baseProj ν) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← baseProj_sub]
  have hle : ‖baseProj ν (x - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [norm_sq_baseProj (x - y) hν]
    nlinarith [sq_nonneg (⟪x - y, ν⟫)]
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-! ### Openness and frontier -/

lemma isOpen_cylinder (z ν : E) (r h : ℝ) : IsOpen (cylinder z ν r h) := by
  have h1 : Continuous fun x : E => ‖baseProj ν (x - z)‖ :=
    ((continuous_baseProj ν).comp (continuous_id.sub continuous_const)).norm
  have h2 : Continuous fun x : E => |⟪x - z, ν⟫| := (continuous_heightComp z ν).abs
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)

lemma isOpen_strictEpigraph {φ : E → ℝ} (hφ : Continuous φ) (z ν : E) :
    IsOpen (strictEpigraph z ν φ) :=
  isOpen_lt (continuous_graphComp hφ z ν) (continuous_heightComp z ν)

/-- For a continuous graph function and a unit normal, the frontier of the strict epigraph is
exactly the graph. -/
lemma frontier_strictEpigraph {φ : E → ℝ} (hφ : Continuous φ) {ν : E} (hν : ‖ν‖ = 1) (z : E) :
    frontier (strictEpigraph z ν φ) = graphSet z ν φ := by
  apply subset_antisymm
  · -- `⊆`: the frontier of a strict-inequality set is contained in the equality set.
    exact frontier_lt_subset_eq (continuous_graphComp hφ z ν) (continuous_heightComp z ν)
  · -- `⊇`: a graph point is approached from strictly inside along `+ν`, and is not itself inside.
    intro p hp
    simp only [graphSet, mem_ofPred_eq] at hp
    have hopen := isOpen_strictEpigraph hφ z ν
    have hpe : p ∉ strictEpigraph z ν φ := by
      simp only [strictEpigraph, mem_ofPred_eq, hp]; exact lt_irrefl _
    have hcont : Continuous fun t : ℝ => p + t • ν :=
      continuous_const.add (continuous_id.smul continuous_const)
    have htend : Tendsto (fun t : ℝ => p + t • ν) (𝓝[>] 0) (𝓝 p) := by
      have h0 : Tendsto (fun t : ℝ => p + t • ν) (𝓝 0) (𝓝 (p + (0 : ℝ) • ν)) := hcont.tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    have hcl : p ∈ closure (strictEpigraph z ν φ) := by
      refine mem_closure_of_tendsto htend ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      simp only [strictEpigraph, mem_ofPred_eq]
      have hrw : p + t • ν - z = (p - z) + t • ν := by abel
      rw [hrw, baseProj_add, baseProj_smul, baseProj_self_eq_zero hν, smul_zero, add_zero, hp,
        inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hν]
      nlinarith [ht']
    refine ⟨hcl, ?_⟩
    rw [hopen.interior_eq]
    exact hpe

end PDETheory
