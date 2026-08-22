import PDETheory.Analysis.Sobolev.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Divergence of a vector field and the weak divergence-free condition

The `PDETheory.divergence` of `Geometry/Domain/Divergence.lean` is the trace of the derivative of an
`E → E` field (its home is the Gauss–Green statement). For fluid problems the velocity is a
`𝕜`-valued vector field `u : ℝᵈ → 𝕜ᵈ` (with `𝕜 = ℂ` for the Stokes system), whose divergence is the
scalar `div u = ∑ᵢ ∂ᵢ uᵢ`. This file adds that operator and the distributional ("weak")
divergence-free condition that cuts out the solenoidal subspace.

## Main definitions

* `PDETheory.vectorDivergence u x = ∑ i, ∂ᵢ(uᵢ)(x)` — the divergence of `u : ℝᵈ → 𝕜ᵈ`.
* `PDETheory.IsWeaklyDivFree Ω μ u` — `∫_Ω ∑ᵢ (∂ᵢψ) • uᵢ = 0` for every scalar test function `ψ`,
  i.e. `div u = 0` in the sense of distributions.
-/

open scoped ContDiff ENNReal
open MeasureTheory

namespace PDETheory

variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The **divergence** of a vector field `u : ℝᵈ → 𝕜ᵈ`: `div u x = ∑ i, ∂ᵢ(uᵢ)(x)`. The `ℝ`-Fréchet
derivative is used throughout — it is defined even for `𝕜`-valued `u`, since `𝕜` is an `ℝ`-vector
space — and equals `0` where `u` is not differentiable. -/
noncomputable def vectorDivergence (u : EuclideanSpace ℝ (Fin d) → (Fin d → 𝕜))
    (x : EuclideanSpace ℝ (Fin d)) : 𝕜 :=
  ∑ i, fderiv ℝ (fun y => u y i) x (EuclideanSpace.single i (1 : ℝ))

@[simp] theorem vectorDivergence_const (c : Fin d → 𝕜) :
    vectorDivergence (fun _ : EuclideanSpace ℝ (Fin d) => c) = 0 := by
  ext x
  simp only [vectorDivergence, fderiv_const_apply, zero_apply,
    Finset.sum_const_zero, Pi.zero_apply]

theorem vectorDivergence_add {u v : EuclideanSpace ℝ (Fin d) → (Fin d → 𝕜)}
    {x : EuclideanSpace ℝ (Fin d)}
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    vectorDivergence (u + v) x = vectorDivergence u x + vectorDivergence v x := by
  simp only [vectorDivergence, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (fun y => (u + v) y i) = (fun y => u y i) + (fun y => v y i) from rfl,
    fderiv_add (hu i) (hv i)]
  rfl

theorem vectorDivergence_smul (a : 𝕜) {u : EuclideanSpace ℝ (Fin d) → (Fin d → 𝕜)}
    {x : EuclideanSpace ℝ (Fin d)} (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x) :
    vectorDivergence (a • u) x = a * vectorDivergence u x := by
  simp only [vectorDivergence, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (fun y => (a • u) y i) = (fun y => a • u y i) from rfl,
    fderiv_fun_const_smul (hu i) a, smul_apply, smul_eq_mul]

/-- **Weakly divergence-free** on `Ω`: for every scalar test function `ψ`,
`∫_Ω ∑ᵢ (∂ᵢψ) • uᵢ = 0` — the distributional statement `div u = 0`. This is the constraint of the
solenoidal space. -/
def IsWeaklyDivFree (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → (Fin d → 𝕜)) : Prop :=
  ∀ ψ : EuclideanSpace ℝ (Fin d) → ℝ, IsTestFn Ω ψ →
    ∫ x in Ω, ∑ i, (fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) • u x i ∂μ = 0

end PDETheory
