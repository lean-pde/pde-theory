import PDETheory.Geometry.Domain.Normal
import PDETheory.Geometry.Domain.Bounded

/-!
# The divergence theorem on Lipschitz domains — operator and statement

This file provides the **divergence operator** and the **statement** of the Gauss–Green (divergence)
theorem for the domains of this development. It does *not* prove the theorem for Lipschitz domains:
that is a major result which mathlib currently has only for boxes
(`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`), and whose extension to Lipschitz
domains requires infrastructure not yet available (a boundary surface-integral / area formula, a
coordinate-free almost-everywhere outward normal — i.e. rectifiability / sets of finite perimeter —
a partition of unity subordinate to a boundary atlas, and the chart-wise integration by parts). The
present file fixes the precise target so that development can proceed against a stable API.

## Main definitions

* `PDETheory.divergence F x = tr (DF x)` — the divergence of a vector field `F : E → E`, defined
  coordinate-freely as the trace of the Fréchet derivative.
* `PDETheory.HasGaussGreen Ω n F` — the divergence-theorem identity for `Ω`, an (explicitly supplied)
  outward normal field `n`, and vector field `F`:
  `∫_Ω div F dx = ∫_{∂Ω} ⟪F, n⟫ dσ`, with the volume the `dim`-dimensional Hausdorff (= Haar)
  measure and `dσ` the surface measure `μH[dim-1] ∣ ∂Ω`.

## Implementation notes

The outward normal is taken as *explicit data* `n : E → E` rather than derived, precisely because a
canonical a.e. normal on a merely-Lipschitz boundary needs the rectifiability theory mathlib lacks.
For a Lipschitz graph the normal is supplied in chart coordinates by
`PDETheory.graphNormal` / `PDETheory.outwardNormal` (see `Normal.lean`); assembling these into a
global `n` and proving `HasGaussGreen` is future work.
-/

open scoped RealInnerProductSpace MeasureTheory
open MeasureTheory Module

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **divergence** of a vector field `F : E → E`, defined coordinate-freely as the trace of its
Fréchet derivative `DF x : E →L[ℝ] E`. Where `F` is not differentiable the derivative is `0`, so the
divergence is `0` there. -/
noncomputable def divergence (F : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ F x).toLinearMap

@[simp]
theorem divergence_const (c : E) : divergence (fun _ : E => c) = 0 := by
  ext x
  simp [divergence, fderiv_const_apply]

/-- The divergence of a sum is the sum of divergences, where both fields are differentiable. -/
theorem divergence_add {F G : E → E} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    divergence (F + G) x = divergence F x + divergence G x := by
  have h : (fderiv ℝ (F + G) x).toLinearMap
      = (fderiv ℝ F x).toLinearMap + (fderiv ℝ G x).toLinearMap := by
    rw [fderiv_add hF hG]; rfl
  simp only [divergence, h, map_add]

section GaussGreen

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- **The Gauss–Green / divergence theorem, as a statement.** For a domain `Ω`, a bundled outward
unit normal field `ν : OutwardNormal Ω` on `∂Ω`, and a vector field `F : E → E`:
`∫_Ω div F dx = ∫_{∂Ω} ⟪F, ν⟫ dσ`,
where the volume on `Ω` is `μHE[dim]` — the Euclidean-normalized Hausdorff measure, equal to
Lebesgue volume — and `dσ` is the surface measure `μHE[dim-1] ∣ ∂Ω` (`surfaceMeasure`). Both use the
Euclidean normalization `μHE`, not raw `μH`, so that the identity is geometrically correct in every
dimension (see `PDETheory.surfaceMeasure`).

The normal is a bundled `PDETheory.OutwardNormal Ω` rather than a bare function, so the boundary flux
`∫_{∂Ω} ⟪F, ν⟫ dσ` is a genuine outward flux (measurable integrand, unit oriented field) rather than
meaningless. Note however that `OutwardNormal.isOutward` pins only the orientation; establishing the
*identity* additionally requires `ν` to be the exact geometric normal `σ`-a.e. (the transported chart
normal `graphNormal`), which the eventual theorem will impose.

This is the identity to be established for Lipschitz (and smoother) domains and suitable `F`; it is
provided here as the target of the development, not yet proved. -/
def HasGaussGreen (Ω : Set E) (ν : OutwardNormal Ω) (F : E → E) : Prop :=
  ∫ x in Ω, divergence F x ∂(μHE[finrank ℝ E])
    = ∫ x in frontier Ω, ⟪F x, ν x⟫ ∂(surfaceMeasure Ω)

end GaussGreen

end PDETheory
