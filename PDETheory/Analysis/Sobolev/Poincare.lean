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
* `PDETheory.poincare_H10` : its extension to `H¹₀`, in sequence form against the `MemW1p0`
  approximation data (`u` an `L²`-limit of test fields whose gradients converge to `g`).
-/

open scoped ContDiff ENNReal NNReal Topology
open MeasureTheory Module Filter

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
    ∃ C : ℝ≥0, ∀ φ : E → F, IsTestField Ω φ →
      eLpNorm φ 2 μ ≤ (C : ℝ≥0∞) * eLpNorm (fun x => fderiv ℝ φ x) 2 μ := by
  refine ⟨eLpNormLESNormFDerivOfLeConst F μ Ω 2 2, fun φ hφ => ?_⟩
  exact eLpNorm_le_eLpNorm_fderiv_of_le (μ := μ)
    (hu := hφ.contDiff.of_le (mod_cast le_top))
    (h2u := (subset_tsupport φ).trans hφ.tsupport_subset)
    (hp := one_le_two)
    (h2p := by exact_mod_cast hd)
    (hpq := sub_le_self _ (by positivity))
    (hs := hΩ)

/-- **Poincaré inequality on `H¹₀`** (sequence form, matching `MemW1p0`). If `u` is an `L²(Ω)`-limit
of test fields `φ n` whose gradients converge to `g` in `L²(Ω)`, then `‖u‖_{L²(Ω)} ≤ C · ‖g‖_{L²(Ω)}`
with the same constant `C` from `poincare_testField`. The hypotheses are exactly the approximation
data packaged in `MemW1p0 Ω μ 2 u` (with `g` its closure gradient), so this lifts Poincaré from test
fields to all of `H¹₀(Ω)`. All norms are the `L²(Ω)` seminorm `eLpNormOn` (the restricted measure),
so the bound is stated in the same currency the domain theory (and downstream coercivity) uses. -/
theorem poincare_H10 {Ω : Set E} (hΩ : Bornology.IsBounded Ω) (hd : 2 < finrank ℝ E)
    [μ.IsAddHaarMeasure] :
    ∃ C : ℝ≥0, ∀ (u : E → F) (φ : ℕ → E → F) (g : E → (E →L[ℝ] F)),
      (∀ n, IsTestField Ω (φ n)) →
      AEStronglyMeasurable u (μ.restrict Ω) → AEStronglyMeasurable g (μ.restrict Ω) →
      Tendsto (fun n => eLpNormOn Ω μ 2 (fun x => φ n x - u x)) atTop (𝓝 0) →
      Tendsto (fun n => eLpNormOn Ω μ 2 (fun x => fderiv ℝ (φ n) x - g x)) atTop (𝓝 0) →
      eLpNormOn Ω μ 2 u ≤ (C : ℝ≥0∞) * eLpNormOn Ω μ 2 g := by
  obtain ⟨C, hC⟩ := poincare_testField (F := F) (μ := μ) hΩ hd
  refine ⟨C, fun u φ g hφ hu_m hg_m hu hg => ?_⟩
  -- Unfold `eLpNormOn` to the restricted-measure `eLpNorm`, and rephrase the approximation data
  -- with pointwise-subtraction (`Pi`) functions (definitionally the same as the `fun x => …` forms).
  simp only [eLpNormOn] at hu hg ⊢
  have huP : Tendsto (fun n => eLpNorm (φ n - u) 2 (μ.restrict Ω)) atTop (𝓝 0) := hu
  have hgP : Tendsto (fun n => eLpNorm (fderiv ℝ (φ n) - g) 2 (μ.restrict Ω)) atTop (𝓝 0) := hg
  have hp12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  -- A test field and its derivative are supported in `Ω`, so their `L²(Ω)` and whole-`L²` norms
  -- agree; this transfers `poincare_testField` (a whole-space bound) to the restricted measure.
  have hsuppφ : ∀ n, Function.support (φ n) ⊆ Ω := fun n =>
    (subset_tsupport (φ n)).trans (hφ n).tsupport_subset
  -- Per `n`: bound `‖u‖` by the two vanishing gaps plus `C‖g‖`.
  have key : ∀ n, eLpNorm u 2 (μ.restrict Ω) ≤
      eLpNorm (φ n - u) 2 (μ.restrict Ω) +
        ((C : ℝ≥0∞) * eLpNorm (fderiv ℝ (φ n) - g) 2 (μ.restrict Ω) +
          (C : ℝ≥0∞) * eLpNorm g 2 (μ.restrict Ω)) := by
    intro n
    have hφm : AEStronglyMeasurable (φ n) (μ.restrict Ω) := (hφ n).continuous.aestronglyMeasurable
    have hdφm : AEStronglyMeasurable (fderiv ℝ (φ n)) (μ.restrict Ω) :=
      ((hφ n).contDiff.continuous_fderiv (by simp)).aestronglyMeasurable
    -- Poincaré on the test field `φ n`, transferred to the restricted measure via support.
    have hCn : eLpNorm (φ n) 2 (μ.restrict Ω) ≤
        (C : ℝ≥0∞) * eLpNorm (fderiv ℝ (φ n)) 2 (μ.restrict Ω) := by
      have hφeq : eLpNorm (φ n) 2 (μ.restrict Ω) = eLpNorm (φ n) 2 μ :=
        eLpNormOn_eq_eLpNorm_of_support_subset (hsuppφ n)
      have hdeq : eLpNorm (fderiv ℝ (φ n)) 2 (μ.restrict Ω) = eLpNorm (fderiv ℝ (φ n)) 2 μ := by
        apply eLpNormOn_eq_eLpNorm_of_support_subset
        intro x hx
        rw [Function.mem_support] at hx
        exact not_not.1 fun hxΩ =>
          hx (fderiv_of_notMem_tsupport ℝ fun h => hxΩ ((hφ n).tsupport_subset h))
      rw [hφeq, hdeq]
      exact hC (φ n) (hφ n)
    -- ‖u - φn‖ = ‖φn - u‖
    have e2 : eLpNorm (u - φ n) 2 (μ.restrict Ω) = eLpNorm (φ n - u) 2 (μ.restrict Ω) := by
      rw [← neg_sub (φ n) u, eLpNorm_neg]
    -- ‖u‖ ≤ ‖u - φn‖ + ‖φn‖ = ‖φn - u‖ + ‖φn‖
    have t1 : eLpNorm u 2 (μ.restrict Ω) ≤
        eLpNorm (φ n - u) 2 (μ.restrict Ω) + eLpNorm (φ n) 2 (μ.restrict Ω) := by
      have h := eLpNorm_add_le (hu_m.sub hφm) hφm hp12
      have e1 : u - φ n + φ n = u := by abel
      rw [e1] at h
      rwa [e2] at h
    -- ‖∇φn‖ ≤ ‖∇φn - g‖ + ‖g‖
    have t2 : eLpNorm (fderiv ℝ (φ n)) 2 (μ.restrict Ω) ≤
        eLpNorm (fderiv ℝ (φ n) - g) 2 (μ.restrict Ω) + eLpNorm g 2 (μ.restrict Ω) := by
      have h := eLpNorm_add_le (hdφm.sub hg_m) hg_m hp12
      have e3 : fderiv ℝ (φ n) - g + g = fderiv ℝ (φ n) := by abel
      rwa [e3] at h
    calc eLpNorm u 2 (μ.restrict Ω)
        ≤ eLpNorm (φ n - u) 2 (μ.restrict Ω) + eLpNorm (φ n) 2 (μ.restrict Ω) := t1
      _ ≤ eLpNorm (φ n - u) 2 (μ.restrict Ω) +
            (C : ℝ≥0∞) * eLpNorm (fderiv ℝ (φ n)) 2 (μ.restrict Ω) := by
          gcongr
      _ ≤ eLpNorm (φ n - u) 2 (μ.restrict Ω) +
            ((C : ℝ≥0∞) * eLpNorm (fderiv ℝ (φ n) - g) 2 (μ.restrict Ω) +
              (C : ℝ≥0∞) * eLpNorm g 2 (μ.restrict Ω)) := by
          rw [← mul_add]; gcongr
  -- RHS → 0 + (C·0 + C‖g‖) = C‖g‖.
  have hlim : Tendsto (fun n => eLpNorm (φ n - u) 2 (μ.restrict Ω) +
      ((C : ℝ≥0∞) * eLpNorm (fderiv ℝ (φ n) - g) 2 (μ.restrict Ω) +
        (C : ℝ≥0∞) * eLpNorm g 2 (μ.restrict Ω)))
      atTop (𝓝 ((C : ℝ≥0∞) * eLpNorm g 2 (μ.restrict Ω))) := by
    have hg' : Tendsto
        (fun n => (C : ℝ≥0∞) * eLpNorm (fderiv ℝ (φ n) - g) 2 (μ.restrict Ω)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hgP (Or.inr (by simp))
      simpa using h
    have hconst : Tendsto (fun _ : ℕ => (C : ℝ≥0∞) * eLpNorm g 2 (μ.restrict Ω)) atTop
        (𝓝 ((C : ℝ≥0∞) * eLpNorm g 2 (μ.restrict Ω))) := tendsto_const_nhds
    have := (huP.add (hg'.add hconst))
    simpa using this
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim key

end PDETheory
