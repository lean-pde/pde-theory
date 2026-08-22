import PDETheory.Analysis.Sobolev.WeakDeriv

/-!
# The Sobolev spaces `Lᵖ(Ω)` and `W^{1,p}(Ω)` / `H¹(Ω)`

Predicate-level Sobolev membership on a domain `Ω`, w.r.t. an ambient Haar measure `μ`:

* `PDETheory.MemLpOn Ω μ p f` : `f ∈ Lᵖ(Ω)` — a thin wrapper over `MeasureTheory.MemLp` for the
  restricted measure `μ.restrict Ω`, inheriting all of its algebra.
* `PDETheory.MemW1p Ω μ p u` : `u ∈ W^{1,p}(Ω)` — `u ∈ Lᵖ(Ω)` and it has a weak Fréchet derivative
  `u' : E → (E →L[ℝ] F)` (`PDETheory.IsWeakDeriv`) with `u' ∈ Lᵖ(Ω)`.
* `PDETheory.MemH1 Ω μ u := MemW1p Ω μ 2 u`.

## Main results

* `PDETheory.IsTestField.memW1p` : every test field lies in `W^{1,p}(Ω)` — the worked example.
-/

open scoped ContDiff ENNReal NNReal
open MeasureTheory

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure E}

/-- `f ∈ Lᵖ(Ω)`: membership in `Lᵖ` for the measure `μ` restricted to `Ω`. -/
def MemLpOn (Ω : Set E) (μ : Measure E) (p : ℝ≥0∞) (f : E → G) : Prop :=
  MemLp f p (μ.restrict Ω)

/-- The `Lᵖ(Ω)` seminorm: the `eLpNorm` for the measure restricted to `Ω`. -/
noncomputable def eLpNormOn (Ω : Set E) (μ : Measure E) (p : ℝ≥0∞) (f : E → G) : ℝ≥0∞ :=
  eLpNorm f p (μ.restrict Ω)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ G] in
/-- The `Lᵖ(Ω)` seminorm of the zero field is `0`. Proved generically over the codomain so it can be
applied to `(E →L[ℝ] F)`-valued fields without an expensive `isDefEq` on the operator-norm space. -/
@[simp] lemma eLpNormOn_zero (Ω : Set E) (μ : Measure E) (p : ℝ≥0∞) :
    eLpNormOn Ω μ p (0 : E → G) = 0 := eLpNorm_zero

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ G] in
/-- If a field is supported in `Ω`, its `Lᵖ(Ω)` seminorm equals its whole-space `Lᵖ` seminorm: the
restriction discards only mass where the field vanishes. Proved generically over the codomain so the
`ENormedAddMonoid`/zero `isDefEq` stays cheap on `(E →L[ℝ] F)`-valued fields (e.g. gradients). -/
theorem eLpNormOn_eq_eLpNorm_of_support_subset {Ω : Set E} {p : ℝ≥0∞} {f : E → G}
    (hf : Function.support f ⊆ Ω) : eLpNormOn Ω μ p f = eLpNorm f p μ :=
  eLpNorm_restrict_eq_of_support_subset hf

/-- `u ∈ W^{1,p}(Ω)`: `u ∈ Lᵖ(Ω)` together with a weak Fréchet derivative in `Lᵖ(Ω)`. -/
def MemW1p (Ω : Set E) (μ : Measure E) (p : ℝ≥0∞) (u : E → F) : Prop :=
  MemLpOn Ω μ p u ∧ ∃ u' : E → (E →L[ℝ] F), IsWeakDeriv Ω μ u u' ∧ MemLpOn Ω μ p u'

/-- `u ∈ H¹(Ω) = W^{1,2}(Ω)`. -/
abbrev MemH1 (Ω : Set E) (μ : Measure E) (u : E → F) : Prop := MemW1p Ω μ 2 u

variable {Ω : Set E} {p : ℝ≥0∞}

section Proj
omit [BorelSpace E] [FiniteDimensional ℝ E]

lemma MemW1p.memLpOn {u : E → F} (h : MemW1p Ω μ p u) : MemLpOn Ω μ p u := h.1

lemma MemW1p.exists_weakDeriv {u : E → F} (h : MemW1p Ω μ p u) :
    ∃ u' : E → (E →L[ℝ] F), IsWeakDeriv Ω μ u u' ∧ MemLpOn Ω μ p u' := h.2

end Proj

/-- **Every test field lies in `W^{1,p}(Ω)`.** Its weak derivative is its classical Fréchet
derivative, which is continuous and compactly supported (hence in every `Lᵖ`). -/
theorem IsTestField.memW1p {φ : E → F} (hφ : IsTestField Ω φ) [μ.IsAddHaarMeasure] :
    MemW1p Ω μ p φ := by
  refine ⟨(hφ.memLp p).restrict Ω, fun x => fderiv ℝ φ x,
    contDiff_isWeakDeriv (hφ.contDiff.of_le (mod_cast le_top)), ?_⟩
  have hcont : Continuous (fun x => fderiv ℝ φ x) := hφ.contDiff.continuous_fderiv (by simp)
  have hcs : HasCompactSupport (fun x => fderiv ℝ φ x) := hφ.hasCompactSupport.fderiv ℝ
  exact (hcont.memLp_of_hasCompactSupport hcs).restrict Ω

end PDETheory
