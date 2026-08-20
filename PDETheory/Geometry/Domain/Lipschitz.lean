import PDETheory.Geometry.Domain.Basic

/-!
# Lipschitz domains

Instantiating the boundary-graph core `PDETheory.HasBoundaryGraphOf` at the Lipschitz regularity
class gives the central objects of this development:

* `PDETheory.HasLipschitzBoundaryWith M Ω` : the boundary is locally the graph of an `M`-Lipschitz
  function, with a **uniform** constant `M` across all charts;
* `PDETheory.HasLipschitzBoundary Ω` : `∃ M, HasLipschitzBoundaryWith M Ω`;
* `PDETheory.IsLipschitzDomain Ω` : `IsOpen Ω ∧ HasLipschitzBoundary Ω`;
* `PDETheory.IsSpecialLipschitzDomain Ω` : `Ω` is the strict epigraph of a single globally
  Lipschitz function — the (unbounded) building block of the Coifman–McIntosh–Meyer theory.

## Main results

* `PDETheory.IsSpecialLipschitzDomain.isLipschitzDomain` : a special Lipschitz domain is a
  Lipschitz domain (inhabits `IsLipschitzDomain`).

## References

See Stein, *Singular Integrals and Differentiability Properties of Functions*; Kenig, *Harmonic
Analysis Techniques for Second Order Elliptic Boundary Value Problems*.
-/

open scoped RealInnerProductSpace NNReal
open Set

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Two elementary shift lemmas -/

omit [InnerProductSpace ℝ E] in
/-- Precomposing with a translation and subtracting a constant preserves the Lipschitz constant. -/
lemma lipschitzWith_shift {K : ℝ≥0} {φ : E → ℝ} (hφ : LipschitzWith K φ) (c : E) (d : ℝ) :
    LipschitzWith K (fun w => φ (w + c) - d) := by
  refine LipschitzWith.of_dist_le_mul fun w1 w2 => ?_
  show dist (φ (w1 + c) - d) (φ (w2 + c) - d) ≤ (K : ℝ) * dist w1 w2
  have hdist : dist (φ (w1 + c) - d) (φ (w2 + c) - d) = dist (φ (w1 + c)) (φ (w2 + c)) := by
    rw [Real.dist_eq, Real.dist_eq]; congr 1; ring
  have hdd : dist (w1 + c) (w2 + c) = dist w1 w2 := by
    rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
  rw [hdist]
  calc dist (φ (w1 + c)) (φ (w2 + c)) ≤ (K : ℝ) * dist (w1 + c) (w2 + c) := hφ.dist_le_mul _ _
    _ = (K : ℝ) * dist w1 w2 := by rw [hdd]

/-- Re-basing a strict epigraph from `0` to `z` is absorbed by shifting the graph function. -/
lemma strictEpigraph_shift (z ν : E) (φ : E → ℝ) :
    strictEpigraph z ν (fun w => φ (w + baseProj ν z) - ⟪z, ν⟫) = strictEpigraph 0 ν φ := by
  ext x
  simp only [strictEpigraph, mem_ofPred_eq, sub_zero]
  rw [baseProj_sub, show baseProj ν x - baseProj ν z + baseProj ν z = baseProj ν x from by abel,
    inner_sub_left]
  constructor <;> intro h <;> linarith

/-! ### Definitions -/

/-- The boundary of `Ω` is locally the graph of an `M`-Lipschitz function, with a **uniform**
constant `M` across all charts. -/
def HasLipschitzBoundaryWith (M : ℝ≥0) (Ω : Set E) : Prop :=
  HasBoundaryGraphOf (LipschitzWith M) Ω

/-- The boundary of `Ω` is locally a Lipschitz graph (for some uniform constant). -/
def HasLipschitzBoundary (Ω : Set E) : Prop :=
  ∃ M, HasLipschitzBoundaryWith M Ω

/-- `Ω` is a Lipschitz domain: open, with a locally Lipschitz-graph boundary. -/
def IsLipschitzDomain (Ω : Set E) : Prop :=
  IsOpen Ω ∧ HasLipschitzBoundary Ω

/-- A *special* Lipschitz domain: the strict epigraph of a single globally Lipschitz function
`φ` over the hyperplane `ν^⟂`. -/
def IsSpecialLipschitzDomain (Ω : Set E) : Prop :=
  ∃ (ν : E) (φ : E → ℝ) (K : ℝ≥0), ‖ν‖ = 1 ∧ LipschitzWith K φ ∧ Ω = strictEpigraph 0 ν φ

variable {Ω : Set E}

/-! ### Extraction lemmas -/

lemma IsLipschitzDomain.isOpen (h : IsLipschitzDomain Ω) : IsOpen Ω := h.1

lemma HasLipschitzBoundary.of_with {M : ℝ≥0} (h : HasLipschitzBoundaryWith M Ω) :
    HasLipschitzBoundary Ω := ⟨M, h⟩

/-- Enlarging the uniform constant preserves the Lipschitz-boundary condition. -/
lemma HasLipschitzBoundaryWith.mono {M₁ M₂ : ℝ≥0} (hM : M₁ ≤ M₂)
    (h : HasLipschitzBoundaryWith M₁ Ω) : HasLipschitzBoundaryWith M₂ Ω :=
  HasBoundaryGraphOf.mono_pred (fun _ hφ => hφ.weaken hM) h

lemma isLipschitzDomain_iff : IsLipschitzDomain Ω ↔ IsOpen Ω ∧ ∃ M, HasLipschitzBoundaryWith M Ω :=
  Iff.rfl

/-! ### A special Lipschitz domain is a Lipschitz domain -/

/-- The strict epigraph of a globally Lipschitz function is a Lipschitz domain. -/
theorem IsSpecialLipschitzDomain.isLipschitzDomain (h : IsSpecialLipschitzDomain Ω) :
    IsLipschitzDomain Ω := by
  obtain ⟨ν, φ, K, hν, hφ, hΩ⟩ := h
  have hcont : Continuous φ := hφ.continuous
  refine ⟨by rw [hΩ]; exact isOpen_strictEpigraph hcont 0 ν, K, ?_⟩
  intro z _hz
  set φ' : E → ℝ := fun w => φ (w + baseProj ν z) - ⟪z, ν⟫ with hφ'
  have hφ'lip : LipschitzWith K φ' := lipschitzWith_shift hφ (baseProj ν z) ⟪z, ν⟫
  have hEq : Ω = strictEpigraph z ν φ' := by
    rw [hΩ]; exact (strictEpigraph_shift z ν φ).symm
  refine ⟨ν, φ', 1, (K : ℝ) + |φ' 0| + 1, hν, one_pos, by positivity, hφ'lip, ?_, ?_⟩
  · intro y _hy0 hy
    have hlip := hφ'lip.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right] at hlip
    have htri : |φ' y| ≤ |φ' y - φ' 0| + |φ' 0| := by
      simpa using abs_add_le (φ' y - φ' 0) (φ' 0)
    have hKy : (K : ℝ) * ‖y‖ ≤ (K : ℝ) := mul_le_of_le_one_right (NNReal.coe_nonneg K) hy.le
    linarith
  · rw [hEq]

end PDETheory
