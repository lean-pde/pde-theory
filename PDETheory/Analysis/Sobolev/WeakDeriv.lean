import PDETheory.Analysis.Sobolev.TestFunction
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Weak (distributional) derivatives on a domain

Working coordinate-freely on an abstract finite-dimensional real normed space `E`, the **weak
derivative** of `u : E → F` is a field `u' : E → (E →L[ℝ] F)` satisfying the integration-by-parts
identity against test functions: for every direction `v` and every scalar test function `ψ`,
`∫_Ω (D_v ψ) • u = - ∫_Ω ψ • (u' · v)`. The coordinate partial `∂ⱼ` is the special case `v = eⱼ`.

## Main definitions

* `PDETheory.IsWeakDerivDir Ω μ v u g` : `g` is the weak derivative of `u` in the direction `v`.
* `PDETheory.IsWeakDeriv Ω μ u u'` : `u'` is the full (coordinate-free) weak Fréchet derivative.

## Main results

* `PDETheory.contDiff_isWeakDeriv` : a `C¹` field's classical Fréchet derivative is its weak
  derivative — the base case linking classical and weak calculus (the module's worked example).
-/

open scoped ContDiff ENNReal NNReal
open MeasureTheory

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E}

/-- `g` is the **weak derivative of `u` in the direction `v`** on `Ω`: for every scalar test function
`ψ`, `∫_Ω (D_v ψ) • u = - ∫_Ω ψ • g`. -/
def IsWeakDerivDir (Ω : Set E) (μ : Measure E) (v : E) (u g : E → F) : Prop :=
  ∀ ψ : E → ℝ, IsTestFn Ω ψ →
    ∫ x in Ω, (fderiv ℝ ψ x v) • u x ∂μ = - ∫ x in Ω, ψ x • g x ∂μ

/-- `u'` is the **weak (Fréchet) derivative** of `u` on `Ω`: it is the weak directional derivative in
every direction `v`. -/
def IsWeakDeriv (Ω : Set E) (μ : Measure E) (u : E → F) (u' : E → (E →L[ℝ] F)) : Prop :=
  ∀ v : E, IsWeakDerivDir Ω μ v u (fun x => u' x v)

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A field whose support lies inside the support of a test field is compactly supported. -/
private lemma hasCompactSupport_of_support_subset {G : Type*} [Zero G] [TopologicalSpace G]
    {ψ : E → ℝ} {h : E → G} (hψ : HasCompactSupport ψ)
    (hsub : Function.support h ⊆ tsupport ψ) : HasCompactSupport h :=
  IsCompact.of_isClosed_subset hψ isClosed_closure
    ((closure_mono hsub).trans (isClosed_closure.closure_eq.le))

/-- **A `C¹` field's Fréchet derivative is its weak derivative.** This is the base case tying the
classical and weak notions together. -/
theorem contDiff_isWeakDeriv {Ω : Set E} {u : E → F} (hu : ContDiff ℝ 1 u) [μ.IsAddHaarMeasure] :
    IsWeakDeriv Ω μ u (fun x => fderiv ℝ u x) := by
  intro v ψ hψ
  have hTop : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have huc : Continuous u := hu.continuous
  have hcψ : Continuous ψ := hψ.continuous
  have hc_dψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.contDiff.continuous_fderiv hTop).clm_apply continuous_const
  have hc_du : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- Support facts: each integrand vanishes off `tsupport ψ`.
  have hcs1 : HasCompactSupport (fun x => fderiv ℝ ψ x v • u x) := by
    refine hasCompactSupport_of_support_subset hψ.hasCompactSupport (fun x hx => ?_)
    by_contra hxs
    have hz : fderiv ℝ ψ x = 0 := fderiv_of_notMem_tsupport ℝ hxs
    exact hx (by simp [hz])
  have hcs2 : HasCompactSupport (fun x => ψ x • fderiv ℝ u x v) := by
    refine hasCompactSupport_of_support_subset hψ.hasCompactSupport (fun x hx => ?_)
    by_contra hxs
    have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxs
    exact hx (by simp [hz])
  have hcs3 : HasCompactSupport (fun x => ψ x • u x) := by
    refine hasCompactSupport_of_support_subset hψ.hasCompactSupport (fun x hx => ?_)
    by_contra hxs
    have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxs
    exact hx (by simp [hz])
  have hi1 : Integrable (fun x => fderiv ℝ ψ x v • u x) μ :=
    (hc_dψ.smul huc).integrable_of_hasCompactSupport hcs1
  have hi2 : Integrable (fun x => ψ x • fderiv ℝ u x v) μ :=
    (hcψ.smul hc_du).integrable_of_hasCompactSupport hcs2
  have hi3 : Integrable (fun x => ψ x • u x) μ :=
    (hcψ.smul huc).integrable_of_hasCompactSupport hcs3
  -- Reduce the set integrals over `Ω` to integrals over the whole space.
  have hL : ∫ x in Ω, (fderiv ℝ ψ x v) • u x ∂μ = ∫ x, (fderiv ℝ ψ x v) • u x ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    have hxs : x ∉ tsupport ψ := fun h => hx (hψ.tsupport_subset h)
    have hz : fderiv ℝ ψ x = 0 := fderiv_of_notMem_tsupport ℝ hxs
    simp [hz]
  have hR : ∫ x in Ω, ψ x • (fderiv ℝ u x v) ∂μ = ∫ x, ψ x • (fderiv ℝ u x v) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    have hxs : x ∉ tsupport ψ := fun h => hx (hψ.tsupport_subset h)
    have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxs
    simp [hz]
  show ∫ x in Ω, (fderiv ℝ ψ x v) • u x ∂μ = - ∫ x in Ω, ψ x • (fderiv ℝ u x v) ∂μ
  rw [hL, hR]
  have H := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (f := ψ) (g := u) (v := v)
    (μ := μ) hi1 hi2 hi3
    (fun x _ => (hψ.contDiff.differentiable hTop).differentiableAt)
    (fun x _ => (hu.differentiable one_ne_zero).differentiableAt)
  rw [H, neg_neg]

end PDETheory
