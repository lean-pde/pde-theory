import PDETheory.Geometry.Domain.Basic

/-!
# Surface measure on a Lipschitz boundary

The boundary graph over a hyperplane `ν^⟂` is the image of the parametrisation
`graphParam z ν φ : u ↦ z + u + φ u • ν`. When `φ` is `K`-Lipschitz this map is
`√(1 + K²)`-Lipschitz on `ν^⟂` (Pythagoras: the vertical stretch adds `K²` under the square root),
so a Lipschitz graph does not inflate Hausdorff measure by more than a fixed factor. This is the
geometric input to the theory of the **surface measure** `σ = μH[dim - 1] ∣ ∂Ω`.

## Main results

* `PDETheory.lipschitzOnWith_graphParam` : the graph parametrisation is `√(1+K²)`-Lipschitz on the
  hyperplane.
* `PDETheory.graphSet_eq_image` : the local graph is the image of the hyperplane under `graphParam`.
* `PDETheory.hausdorffMeasure_graphSet_le` : the Hausdorff-measure bound for the graph.
* `PDETheory.surfaceMeasure` : the surface measure on `∂Ω`.
-/

open scoped RealInnerProductSpace NNReal ENNReal MeasureTheory
open Set MeasureTheory

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hyperplane `ν^⟂ = {u | ⟪u, ν⟫ = 0}`. -/
def hyperplane (ν : E) : Set E := {u | ⟪u, ν⟫ = 0}

/-- Parametrisation of the graph over `ν^⟂` based at `z`: `u ↦ z + u + φ u • ν`. -/
def graphParam (z ν : E) (φ : E → ℝ) : E → E := fun u => z + (u + φ u • ν)

/-- On the hyperplane `ν^⟂`, `baseProj ν` is the identity. -/
lemma baseProj_of_mem_hyperplane {ν u : E} (hu : u ∈ hyperplane ν) : baseProj ν u = u := by
  simp only [hyperplane, mem_ofPred_eq] at hu
  simp [baseProj, hu]

/-- Base projection of `u + s • ν` recovers `u` when `u ⟂ ν` and `‖ν‖ = 1`. -/
lemma baseProj_add_smul_self {ν u : E} (hu : u ∈ hyperplane ν) (hν : ‖ν‖ = 1) (s : ℝ) :
    baseProj ν (u + s • ν) = u := by
  simp only [hyperplane, mem_ofPred_eq] at hu
  simp only [baseProj, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu, hν]
  module

/-- The graph parametrisation is `√(1 + K²)`-Lipschitz on the hyperplane. -/
lemma lipschitzOnWith_graphParam {ν : E} (hν : ‖ν‖ = 1) {φ : E → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (z : E) :
    LipschitzOnWith (Real.sqrt (1 + (K : ℝ) ^ 2)).toNNReal (graphParam z ν φ) (hyperplane ν) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u₁ h₁ u₂ h₂
  simp only [hyperplane, mem_ofPred_eq] at h₁ h₂
  have ha : ⟪u₁ - u₂, ν⟫ = 0 := by rw [inner_sub_left, h₁, h₂, sub_zero]
  have hdiff : graphParam z ν φ u₁ - graphParam z ν φ u₂
      = (u₁ - u₂) + (φ u₁ - φ u₂) • ν := by simp only [graphParam]; module
  have hs : ‖((φ u₁ - φ u₂) • ν : E)‖ = |φ u₁ - φ u₂| := by
    rw [norm_smul, Real.norm_eq_abs, hν, mul_one]
  have hnormsq : ‖graphParam z ν φ u₁ - graphParam z ν φ u₂‖ ^ 2
      = ‖u₁ - u₂‖ ^ 2 + (φ u₁ - φ u₂) ^ 2 := by
    rw [hdiff, norm_add_sq_real, real_inner_smul_right, ha, mul_zero, mul_zero, add_zero, hs, sq_abs]
  have hlips : (φ u₁ - φ u₂) ^ 2 ≤ (K : ℝ) ^ 2 * ‖u₁ - u₂‖ ^ 2 := by
    have hd := hφ.dist_le_mul u₁ u₂
    rw [Real.dist_eq, dist_eq_norm] at hd
    nlinarith [hd, abs_nonneg (φ u₁ - φ u₂), sq_abs (φ u₁ - φ u₂), norm_nonneg (u₁ - u₂),
      K.coe_nonneg, mul_nonneg K.coe_nonneg (norm_nonneg (u₁ - u₂))]
  have hbound : ‖graphParam z ν φ u₁ - graphParam z ν φ u₂‖ ^ 2 ≤ (1 + (K : ℝ) ^ 2) * ‖u₁ - u₂‖ ^ 2 := by
    rw [hnormsq]; nlinarith [hlips]
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  calc ‖graphParam z ν φ u₁ - graphParam z ν φ u₂‖
      = Real.sqrt (‖graphParam z ν φ u₁ - graphParam z ν φ u₂‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 + (K : ℝ) ^ 2) * ‖u₁ - u₂‖ ^ 2) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (1 + (K : ℝ) ^ 2) * ‖u₁ - u₂‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The local graph is the image of the hyperplane under the graph parametrisation. -/
lemma graphSet_eq_image {ν : E} (hν : ‖ν‖ = 1) (φ : E → ℝ) (z : E) :
    graphSet z ν φ = graphParam z ν φ '' hyperplane ν := by
  ext x
  simp only [graphSet, mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hx
    refine ⟨baseProj ν (x - z), ?_, ?_⟩
    · simp only [hyperplane, mem_ofPred_eq]
      exact inner_baseProj_left (x - z) hν
    · simp only [graphParam]
      rw [hx]
      simp only [baseProj]
      module
  · rintro ⟨u, hu, rfl⟩
    have hu0 : ⟪u, ν⟫ = 0 := hu
    have heq : graphParam z ν φ u - z = u + φ u • ν := by simp only [graphParam]; module
    rw [heq, baseProj_add_smul_self hu hν, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu0, hν]
    ring

variable [MeasurableSpace E] [BorelSpace E]

/-- **Hausdorff-measure bound for a Lipschitz graph.** -/
theorem hausdorffMeasure_graphSet_le {ν : E} (hν : ‖ν‖ = 1) {φ : E → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (z : E) {d : ℝ} (hd : 0 ≤ d) :
    μH[d] (graphSet z ν φ)
      ≤ ((Real.sqrt (1 + (K : ℝ) ^ 2)).toNNReal : ℝ≥0∞) ^ d * μH[d] (hyperplane ν) := by
  rw [graphSet_eq_image hν φ z]
  exact (lipschitzOnWith_graphParam hν hφ z).hausdorffMeasure_image_le hd

/-- Hausdorff-measure bound for the graph over an arbitrary hyperplane subset. -/
theorem hausdorffMeasure_graphParam_image_le {ν : E} (hν : ‖ν‖ = 1) {φ : E → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (z : E) {d : ℝ} (hd : 0 ≤ d) {S : Set E} (hS : S ⊆ hyperplane ν) :
    μH[d] (graphParam z ν φ '' S)
      ≤ ((Real.sqrt (1 + (K : ℝ) ^ 2)).toNNReal : ℝ≥0∞) ^ d * μH[d] S :=
  ((lipschitzOnWith_graphParam hν hφ z).mono hS).hausdorffMeasure_image_le hd

/-- If a hyperplane region has finite `d`-dimensional Hausdorff measure, so does the graph over it.
This reduces surface-measure finiteness on a Lipschitz graph to finiteness on the flat hyperplane
(which holds for bounded regions, since `μH[dim-1]` is a Haar measure on the hyperplane subspace). -/
theorem hausdorffMeasure_graphParam_image_lt_top {ν : E} (hν : ‖ν‖ = 1) {φ : E → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (z : E) {d : ℝ} (hd : 0 ≤ d) {S : Set E} (hS : S ⊆ hyperplane ν)
    (hSfin : μH[d] S < ⊤) : μH[d] (graphParam z ν φ '' S) < ⊤ :=
  lt_of_le_of_lt (hausdorffMeasure_graphParam_image_le hν hφ z hd hS)
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.coe_ne_top) hSfin)

/-- The **surface measure** on `∂Ω`: the `(dim - 1)`-dimensional Hausdorff measure restricted to the
boundary. -/
noncomputable def surfaceMeasure (Ω : Set E) : Measure E :=
  (μH[((Module.finrank ℝ E - 1 : ℕ) : ℝ)]).restrict (frontier Ω)

end PDETheory
