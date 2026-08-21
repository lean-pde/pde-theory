import PDETheory.Analysis.Sobolev.MemW1p0
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# The Poincaré inequality for test fields

On a bounded domain `Ω ⊆ E` (with `dim E ≥ 3`), a compactly-supported field `φ` is controlled in
`L²` by its gradient: `‖φ‖_{L²} ≤ C · ‖∇φ‖_{L²}`, with `C` depending only on `Ω` (and `F`, `μ`), not
on `φ`. This is the **Poincaré (Friedrichs) inequality** — the coercivity input for the Dirichlet
problem.

The proof is a direct application of the Gagliardo–Nirenberg–Sobolev inequality in its
bounded-support form (`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`): with Sobolev exponents
`p = q = 2`, the subcriticality condition `1/2 - 1/dim ≤ 1/2` holds automatically, so the `L²`→`L²`
bound follows without the classical one-dimensional / Fubini argument.

## Main results

* `PDETheory.poincare_testField` : the Poincaré inequality for test fields on a bounded domain.
-/

open scoped ContDiff ENNReal NNReal
open MeasureTheory Module

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E}

/-- **Poincaré inequality for test fields.** On a bounded domain `Ω` in a space of dimension `≥ 3`,
there is a constant `C` (independent of `φ`) with `‖φ‖_{L²} ≤ C · ‖∇φ‖_{L²}` for every test field
`φ`. Since a test field is supported in `Ω`, the whole-space `L²` norms here coincide with the
`L²(Ω)` norms. -/
theorem poincare_testField {Ω : Set E} (hΩ : Bornology.IsBounded Ω) (hd : 2 < finrank ℝ E)
    [μ.IsAddHaarMeasure] :
    ∃ C : ℝ≥0∞, ∀ φ : E → F, IsTestField Ω φ →
      eLpNorm φ 2 μ ≤ C * eLpNorm (fun x => fderiv ℝ φ x) 2 μ := by
  refine ⟨eLpNormLESNormFDerivOfLeConst F μ Ω 2 2, fun φ hφ => ?_⟩
  exact eLpNorm_le_eLpNorm_fderiv_of_le (μ := μ)
    (hu := hφ.contDiff.of_le (mod_cast le_top))
    (h2u := (subset_tsupport φ).trans hφ.tsupport_subset)
    (hp := one_le_two)
    (h2p := by exact_mod_cast hd)
    (hpq := sub_le_self _ (by positivity))
    (hs := hΩ)

end PDETheory
