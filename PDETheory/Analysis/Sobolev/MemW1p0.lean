import PDETheory.Analysis.Sobolev.MemWkp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Data.ENNReal.Holder

/-!
# The zero-trace Sobolev space `W^{1,p}₀(Ω)` / `H¹₀(Ω)`

`W^{1,p}₀(Ω)` is the closure of the compactly-supported smooth fields in the `W^{1,p}` norm — the
functions "vanishing on `∂Ω`". We encode membership as the existence of an approximating sequence of
test fields whose values converge to `u` in `Lᵖ(Ω)` and whose derivatives converge to a common limit
`g` in `Lᵖ(Ω)` (the closure gradient), together with measurability witnesses for `u` and `g`.

## Main definitions

* `PDETheory.MemW1p0 Ω μ p u` : `u ∈ W^{1,p}₀(Ω)`.
* `PDETheory.MemH10 Ω μ u := MemW1p0 Ω μ 2 u`.

## Main results

* `PDETheory.IsTestField.memW1p0` : every test field lies in `W^{1,p}₀(Ω)` (its own constant
  approximating sequence) — the worked example inhabiting the space.
* `PDETheory.memW1p0_memW1p_of_one_le` : the Sobolev embedding `W^{1,p}₀(Ω) ⊆ W^{1,p}(Ω)` for
  `1 ≤ p`.

## Implementation notes

The `AEStronglyMeasurable` witnesses are bundled into the definition so that a member can later be
lifted to an element of the bundled `Lᵖ`-based Hilbert space without re-choosing representatives.
-/

open scoped ContDiff ENNReal NNReal Topology
open MeasureTheory Filter

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E}

/-- `u ∈ W^{1,p}₀(Ω)`: there is a sequence of test fields `φ n` and a field `g : E → (E →L[ℝ] F)`
with `φ n → u` in `Lᵖ(Ω)` and `fderiv (φ n) → g` in `Lᵖ(Ω)`, plus measurability of `u` and `g`. -/
def MemW1p0 (Ω : Set E) (μ : Measure E) (p : ℝ≥0∞) (u : E → F) : Prop :=
  ∃ (φ : ℕ → E → F) (g : E → (E →L[ℝ] F)),
    (∀ n, IsTestField Ω (φ n)) ∧
    Tendsto (fun n => eLpNormOn Ω μ p (fun x => φ n x - u x)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNormOn Ω μ p (fun x => fderiv ℝ (φ n) x - g x)) atTop (𝓝 0) ∧
    AEStronglyMeasurable u (μ.restrict Ω) ∧ AEStronglyMeasurable g (μ.restrict Ω)

/-- `u ∈ H¹₀(Ω) = W^{1,2}₀(Ω)`. -/
abbrev MemH10 (Ω : Set E) (μ : Measure E) (u : E → F) : Prop := MemW1p0 Ω μ 2 u

variable {Ω : Set E} {p : ℝ≥0∞}

/-- **Every test field lies in `W^{1,p}₀(Ω)`**, witnessed by its own constant approximating
sequence. This inhabits the space. -/
theorem IsTestField.memW1p0 {φ : E → F} (hφ : IsTestField Ω φ) : MemW1p0 Ω μ p φ := by
  have hcont_d : Continuous (fun x => fderiv ℝ φ x) := hφ.contDiff.continuous_fderiv (by simp)
  refine ⟨fun _ => φ, fun x => fderiv ℝ φ x, fun _ => hφ, ?_, ?_,
    hφ.continuous.aestronglyMeasurable, hcont_d.aestronglyMeasurable⟩
  · have hz : (fun x => φ x - φ x) = (0 : E → F) := by ext x; simp
    have he : eLpNormOn Ω μ p (fun x => φ x - φ x) = 0 := by rw [hz]; exact eLpNormOn_zero Ω μ p
    simp only [he]; exact tendsto_const_nhds
  · have hz : (fun x => fderiv ℝ φ x - fderiv ℝ φ x) = (0 : E → (E →L[ℝ] F)) := by ext x; simp
    have he : eLpNormOn Ω μ p (fun x => fderiv ℝ φ x - fderiv ℝ φ x) = 0 := by
      rw [hz]; exact eLpNormOn_zero Ω μ p
    simp only [he]; exact tendsto_const_nhds

/-- **Helper: Lᵖ-limit of a sequence stays in Lᵖ.** If approximants `a n` are in `Lᵖ`, a limit `w`
is measurable, and `‖aₙ - w‖_{Lᵖ} → 0`, then `w ∈ Lᵖ`. -/
theorem memLp_limit_of_tendsto {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {p : ℝ≥0∞} {E' : Type*} [NormedAddCommGroup E'] {a : ℕ → α → E'} {w : α → E'}
    (ha : ∀ n, MemLp (a n) p ν) (hw_m : AEStronglyMeasurable w ν)
    (hconv : Tendsto (fun n => eLpNorm (fun x => a n x - w x) p ν) atTop (𝓝 0)) : MemLp w p ν := by
  -- The tail of `hconv` is eventually finite; extract one such index.
  have hev : ∀ᶠ y : ℝ≥0∞ in 𝓝 0, y ≠ ⊤ := by
    filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ≥0∞) ∈ Set.Iio ⊤ by simp)] with y hy
    exact ne_of_lt hy
  obtain ⟨n, hn⟩ := (hconv.eventually hev).exists
  have hdiff : MemLp (a n - w) p ν := ⟨(ha n).1.sub hw_m, lt_top_iff_ne_top.2 hn⟩
  have hmem : MemLp (a n - (a n - w)) p ν := (ha n).sub hdiff
  simpa only [sub_sub_cancel] using hmem

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Helper: Hölder pairing continuity.** For a continuous, compactly supported multiplier `w`,
`1 ≤ p`, and `Lᵖ(μ.restrict Ω)` data with `‖hₙ - v‖_{Lᵖ} → 0`, the scalar pairings `∫ w • hₙ`
converge to `∫ w • v`. With the conjugate exponent `q` (`q⁻¹ + p⁻¹ = 1`), the compactly supported `w`
lies in `Lᵍ`, so Hölder gives `‖∫ w • (hₙ - v)‖ ≤ ‖w‖_{Lᵍ} · ‖hₙ - v‖_{Lᵖ} → 0`. This is what passes
the smooth integration-by-parts identity to the `Lᵖ`-limit. -/
theorem tendsto_integral_smul_of_tendsto_eLpNorm {Ω : Set E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    [μ.IsAddHaarMeasure] {w : E → ℝ} (hw_cont : Continuous w) (hw_cpt : HasCompactSupport w)
    {v : E → F} {h : ℕ → E → F}
    (hv : MemLp v p (μ.restrict Ω)) (hh : ∀ n, MemLp (h n) p (μ.restrict Ω))
    (hconv : Tendsto (fun n => eLpNorm (fun x => h n x - v x) p (μ.restrict Ω)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, w x • h n x ∂(μ.restrict Ω)) atTop
      (𝓝 (∫ x, w x • v x ∂(μ.restrict Ω))) := by
  obtain ⟨q, hHT⟩ : ∃ q : ℝ≥0∞, ENNReal.HolderTriple q p 1 :=
    ⟨(1 - p⁻¹)⁻¹, ⟨by rw [inv_inv, inv_one, tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hp)]⟩⟩
  have := hHT
  have hw_Lp : MemLp w q (μ.restrict Ω) := hw_cont.memLp_of_hasCompactSupport hw_cpt
  have hC_ne : eLpNorm w q (μ.restrict Ω) ≠ ⊤ := hw_Lp.eLpNorm_lt_top.ne
  have hw_m : AEStronglyMeasurable w (μ.restrict Ω) := hw_cont.aestronglyMeasurable
  have hInt_h : ∀ n, Integrable (fun x => w x • h n x) (μ.restrict Ω) := fun n =>
    memLp_one_iff_integrable.1 (MemLp.smul (hh n) hw_Lp)
  have hInt_v : Integrable (fun x => w x • v x) (μ.restrict Ω) :=
    memLp_one_iff_integrable.1 (MemLp.smul hv hw_Lp)
  have hdiff : ∀ n, (∫ x, w x • h n x ∂(μ.restrict Ω)) - ∫ x, w x • v x ∂(μ.restrict Ω)
      = ∫ x, w x • (h n x - v x) ∂(μ.restrict Ω) := by
    intro n
    rw [← integral_sub (hInt_h n) hInt_v]
    congr 1; funext x; rw [smul_sub]
  have hbound : ∀ n, ‖∫ x, w x • (h n x - v x) ∂(μ.restrict Ω)‖ₑ
      ≤ eLpNorm w q (μ.restrict Ω) * eLpNorm (fun x => h n x - v x) p (μ.restrict Ω) := fun n =>
    calc ‖∫ x, w x • (h n x - v x) ∂(μ.restrict Ω)‖ₑ
        ≤ ∫⁻ x, ‖w x • (h n x - v x)‖ₑ ∂(μ.restrict Ω) := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => w x • (h n x - v x)) 1 (μ.restrict Ω) :=
          eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm w q (μ.restrict Ω) * eLpNorm (fun x => h n x - v x) p (μ.restrict Ω) :=
          eLpNorm_smul_le_mul_eLpNorm ((hh n).1.sub hv.1) hw_m
  have hCbn : Tendsto (fun n => eLpNorm w q (μ.restrict Ω)
      * eLpNorm (fun x => h n x - v x) p (μ.restrict Ω)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hconv (Or.inr hC_ne)
    rwa [mul_zero] at this
  have hmid : Tendsto (fun n => ‖∫ x, w x • (h n x - v x) ∂(μ.restrict Ω)‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hCbn (fun _ => zero_le) hbound
  have hreal : Tendsto (fun n => ‖∫ x, w x • (h n x - v x) ∂(μ.restrict Ω)‖) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal_zero_iff (fun _ => enorm_ne_top)).2 hmid
    simpa only [toReal_enorm] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hdiff]
  exact hreal

/-- **`W^{1,p}₀(Ω) ⊆ W^{1,p}(Ω)` for `1 ≤ p`.** A closure-defined member `u` of `W^{1,p}₀`, with
`Lᵖ`-limit `u` of test fields `φₙ` and total-gradient limit `g`, is a genuine `W^{1,p}` field: `u ∈ Lᵖ(Ω)`
and `g` is the weak Fréchet derivative of `u` in `Lᵖ(Ω)`. -/
theorem memW1p0_memW1p_of_one_le {p : ℝ≥0∞} (hp : 1 ≤ p) {u : E → F}
    [μ.IsAddHaarMeasure] (h : MemW1p0 Ω μ p u) : MemW1p Ω μ p u := by
  obtain ⟨φ, g, hφ_test, h2, h3, hu_m, hg_m⟩ := h
  simp only [eLpNormOn] at h2 h3
  -- Value part: `u ∈ Lᵖ(Ω)`.
  have hu_Lp : MemLp u p (μ.restrict Ω) :=
    memLp_limit_of_tendsto (fun n => by
      obtain ⟨hcd, hcpt, _⟩ := hφ_test n
      exact hcd.continuous.memLp_of_hasCompactSupport hcpt) hu_m h2
  -- The closure gradient lies in `Lᵖ(Ω)`.
  have hg_Lp : MemLp g p (μ.restrict Ω) :=
    memLp_limit_of_tendsto (a := fun n x => fderiv ℝ (φ n) x) (fun n => by
      obtain ⟨hcd, hcpt, _⟩ := hφ_test n
      exact (hcd.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
        (hcpt.fderiv ℝ)) hg_m h3
  refine ⟨hu_Lp, g, ?_, hg_Lp⟩
  -- Show that `g` is the weak derivative in every direction.
  intro v ψ ⟨hψ_cd, hψ_cpt, hψ_sub⟩
  -- Apply contDiff_isWeakDeriv to each φₙ to get the integration-by-parts identity.
  have hidn : ∀ n, (∫ x in Ω, (fderiv ℝ ψ x v) • φ n x ∂μ)
      = - ∫ x in Ω, ψ x • (fderiv ℝ (φ n) x v) ∂μ := fun n => by
    obtain ⟨hcd, _, _⟩ := hφ_test n
    exact contDiff_isWeakDeriv (hcd.of_le (by simp)) v ψ ⟨hψ_cd, hψ_cpt, hψ_sub⟩
  -- `Lᵖ` membership of the approximants, their directional partials, and the closure column `g·v`.
  have hφ_Lp : ∀ n, MemLp (φ n) p (μ.restrict Ω) := fun n => by
    obtain ⟨hcd, hcpt, _⟩ := hφ_test n
    exact hcd.continuous.memLp_of_hasCompactSupport hcpt
  have hdv_Lp : ∀ n, MemLp (fun x => fderiv ℝ (φ n) x v) p (μ.restrict Ω) := fun n => by
    obtain ⟨hcd, hcpt, _⟩ := hφ_test n
    exact ((hcd.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hcpt.fderiv_apply ℝ v)
  have hgv_meas : AEStronglyMeasurable (fun x => g x v) (μ.restrict Ω) := by
    have := ((ContinuousLinearMap.apply ℝ F v).continuous).comp_aestronglyMeasurable hg_m
    simpa only [ContinuousLinearMap.apply_apply] using this
  -- `g·v ∈ Lᵖ(Ω)`: dominate by the real field `‖v‖·‖g·‖` (scaling stays on `ℝ`, not on `E →L F`,
  -- so the `eLpNorm`/`MemLp` `isDefEq` never touches the operator-norm space).
  have hgv_Lp : MemLp (fun x => g x v) p (μ.restrict Ω) := by
    refine (hg_Lp.norm.const_smul (‖v‖ : ℝ)).of_le hgv_meas (Filter.Eventually.of_forall fun x => ?_)
    simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_mul, abs_of_nonneg (norm_nonneg v)] using ((g x).le_opNorm v).trans_eq (mul_comm _ _)
  -- `∂_v φₙ → g·v` in `Lᵖ(Ω)`, from `Dφₙ → g` and the operator-norm bound `‖A v‖ ≤ ‖A‖‖v‖`.
  have hconv_v : Tendsto (fun n => eLpNorm (fun x => fderiv ℝ (φ n) x v - g x v) p (μ.restrict Ω))
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun n => ‖(‖v‖ : ℝ)‖ₑ *
        eLpNorm (fun x => fderiv ℝ (φ n) x - g x) p (μ.restrict Ω)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ‖(‖v‖ : ℝ)‖ₑ) h3 (Or.inr (by simp))
      simpa only [mul_zero] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconst
      (fun _ => zero_le) (fun n => ?_)
    have hpt : ∀ x, ‖fderiv ℝ (φ n) x v - g x v‖ ≤ ‖v‖ * ‖fderiv ℝ (φ n) x - g x‖ := fun x => by
      rw [← sub_apply]
      exact ((fderiv ℝ (φ n) x - g x).le_opNorm v).trans_eq (mul_comm _ _)
    calc eLpNorm (fun x => fderiv ℝ (φ n) x v - g x v) p (μ.restrict Ω)
        ≤ eLpNorm ((‖v‖ : ℝ) • fun x => ‖fderiv ℝ (φ n) x - g x‖) p (μ.restrict Ω) := by
          refine eLpNorm_mono (fun x => ?_)
          simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
            abs_mul, abs_of_nonneg (norm_nonneg v)] using hpt x
      _ ≤ ‖(‖v‖ : ℝ)‖ₑ * eLpNorm (fun x => ‖fderiv ℝ (φ n) x - g x‖) p (μ.restrict Ω) :=
          eLpNorm_const_smul_le
      _ = ‖(‖v‖ : ℝ)‖ₑ * eLpNorm (fun x => fderiv ℝ (φ n) x - g x) p (μ.restrict Ω) := by
          rw [eLpNorm_norm]
  -- Both pairings converge; the per-`n` identity `hidn` identifies the two limits.
  have hLHS := tendsto_integral_smul_of_tendsto_eLpNorm hp
    ((hψ_cd.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hψ_cpt.fderiv_apply ℝ v) hu_Lp hφ_Lp h2
  have hRHS := tendsto_integral_smul_of_tendsto_eLpNorm hp hψ_cd.continuous hψ_cpt
    hgv_Lp hdv_Lp hconv_v
  exact tendsto_nhds_unique hLHS (Filter.Tendsto.congr (fun n => (hidn n).symm) hRHS.neg)

end PDETheory
