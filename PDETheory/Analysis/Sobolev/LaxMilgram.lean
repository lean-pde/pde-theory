import PDETheory.Analysis.Sobolev.H10Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Weak-form operators: the Lax–Milgram interface

The weak formulation of an elliptic problem represents a (sesqui)linear form `B` on a Hilbert space
by a bounded operator `A` with `⟪A v, w⟫ = B v w`. This file exposes that representation on top of
mathlib's Riesz/Lax–Milgram API, in the shape the domain theory (and the Stokes application, whose
Dirichlet form is `ℂ`-sesquilinear) consumes it. It applies in particular to the bundled Hilbert
space `↥(H10Space Ω μ 𝕜 m)` of `H10Space.lean`.

## Main definitions / results

* `PDETheory.formOperator B` : for a **bounded sesquilinear form** `B` on a `𝕜`-Hilbert space
  (`RCLike 𝕜`, so `ℂ` in particular), the unique bounded operator with `⟪formOperator B v, w⟫ = B v w`
  (`inner_formOperator`, `eq_formOperator_of_forall_inner`). Wraps
  `InnerProductSpace.continuousLinearMapOfBilin` — the Riesz representation.
* `PDETheory.coerciveEquiv hB` : the **real Lax–Milgram** theorem — a bounded *coercive* bilinear
  form on a real Hilbert space induces a continuous linear *equivalence* (`inner_coerciveEquiv`).
  Wraps `IsCoercive.continuousLinearEquivOfBilin`.

## Implementation notes

The `ℂ`-sesquilinear layer (`formOperator`) gives only the bounded representing operator; it does
**not** claim invertibility. The coercivity ⇒ invertibility upgrade (full Lax–Milgram) is available
here only over `ℝ` (`coerciveEquiv`), because mathlib's `IsCoercive` API is real-only. A complex
coercive Lax–Milgram (needed to solve the Stokes resolvent system as an isomorphism) is a documented
gap, not proved here.
-/

open MeasureTheory

namespace PDETheory

section Sesquilinear

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The bounded operator representing a **bounded sesquilinear form** `B` on a `𝕜`-Hilbert space:
the unique `A : E →L[𝕜] E` with `⟪A v, w⟫ = B v w` (Riesz representation). For the Stokes Dirichlet
form (`𝕜 = ℂ`) this is the bounded operator of the weak formulation. -/
noncomputable def formOperator (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) : E →L[𝕜] E :=
  InnerProductSpace.continuousLinearMapOfBilin B

/-- The defining property of `formOperator`: `⟪formOperator B v, w⟫ = B v w`. -/
theorem inner_formOperator (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) (v w : E) :
    inner 𝕜 (formOperator B v) w = B v w :=
  InnerProductSpace.continuousLinearMapOfBilin_apply B v w

/-- `formOperator B v` is the unique vector representing `B v ·` through the inner product. -/
theorem eq_formOperator_of_forall_inner (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) {v f : E}
    (h : ∀ w, inner 𝕜 f w = B v w) : f = formOperator B v :=
  InnerProductSpace.unique_continuousLinearMapOfBilin B h

end Sesquilinear

section Coercive

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **Lax–Milgram (real, coercive case).** A bounded *coercive* bilinear form `B` on a real Hilbert
space induces a continuous linear *equivalence* `V ≃L[ℝ] V`: the weak operator is invertible, so the
weak problem `B u · = ⟪f, ·⟫` is uniquely solvable. Wraps `IsCoercive.continuousLinearEquivOfBilin`. -/
noncomputable def coerciveEquiv {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B) : V ≃L[ℝ] V :=
  hB.continuousLinearEquivOfBilin

/-- The defining property of `coerciveEquiv`: `⟪coerciveEquiv hB v, w⟫ = B v w`. -/
theorem inner_coerciveEquiv {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B) (v w : V) :
    inner ℝ (coerciveEquiv hB v) w = B v w :=
  hB.continuousLinearEquivOfBilin_apply v w

end Coercive

/-- The interface applies to the bundled `H¹₀(Ω)`: a bounded `ℂ`-sesquilinear form on
`↥(H10Space Ω volume ℂ m)` has a representing bounded operator. -/
example {d m : ℕ} {Ω : Set (Dom d)}
    (B : ↥(H10Space Ω volume ℂ m) →L⋆[ℂ] ↥(H10Space Ω volume ℂ m) →L[ℂ] ℂ) : True := by
  have : ↥(H10Space Ω volume ℂ m) →L[ℂ] ↥(H10Space Ω volume ℂ m) := formOperator B
  trivial

end PDETheory
