import PDETheory.Analysis.Sobolev.MemWkp
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The bundled Lᵖ space on a domain

`MemLpOn`/`eLpNormOn` are predicate/`ℝ≥0∞`-seminorm level. For operator theory (uniqueness,
Lax–Milgram, …) one needs the genuine **bundled** `Lᵖ(Ω)` — a Banach space (a Hilbert space when
`p = 2`), i.e. the `MeasureTheory.Lp` type for the restricted measure. This file introduces the
abbreviation and the `Mem… ↔ ∈` bridge lemmas connecting the predicate layer to it.

## Main definitions / results

* `PDETheory.LpOn Ω μ p F := Lp F p (μ.restrict Ω)` — the bundled `Lᵖ(Ω; F)`.
* `PDETheory.MemLpOn.toLpOn` / `coeFn_toLpOn` / `mem_LpOn_iff_memLpOn` — the bridge.
* `PDETheory.norm_toLpOn` : `‖h.toLpOn‖ = (eLpNormOn Ω μ p f).toReal` — the `ℝ≥0∞ → ℝ` off-ramp.

For `p = 2`, `[RCLike 𝕜] [InnerProductSpace 𝕜 F]`, `LpOn Ω μ 2 F` is a `𝕜`-Hilbert space
(`⟪f,g⟫ = ∫_Ω ⟪f x, g x⟫`) — over `ℂ` in particular — inherited from `L2.innerProductSpace`.
-/

open scoped ENNReal
open MeasureTheory

namespace PDETheory

variable {E : Type*} [MeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F]
  {μ : Measure E} {p : ℝ≥0∞} {Ω : Set E}

/-- The bundled `Lᵖ(Ω; F)`: the `Lp` space for `μ` restricted to `Ω`. Inherits
`NormedAddCommGroup`, `NormedSpace`/`CompleteSpace` (for `[Fact (1 ≤ p)]`), and — for `p = 2` with an
inner-product codomain — an `InnerProductSpace` structure. -/
abbrev LpOn (Ω : Set E) (μ : Measure E) (p : ℝ≥0∞) (F : Type*) [NormedAddCommGroup F] : Type _ :=
  Lp F p (μ.restrict Ω)

@[inherit_doc] scoped notation "L²(" Ω ", " μ ")" => LpOn Ω μ 2

/-- Lift a member function `f` to the bundled space `Lᵖ(Ω)`. -/
noncomputable def MemLpOn.toLpOn {f : E → F} (h : MemLpOn Ω μ p f) : LpOn Ω μ p F :=
  MemLp.toLp f h

/-- The bundled element recovers `f` almost everywhere. -/
theorem MemLpOn.coeFn_toLpOn {f : E → F} (h : MemLpOn Ω μ p f) :
    (h.toLpOn : E → F) =ᵐ[μ.restrict Ω] f :=
  MemLp.coeFn_toLp h

/- For membership of an a.e.-class in the underlying `Lp` subgroup use mathlib's
`MeasureTheory.Lp.mem_Lp_iff_memLp` directly (`LpOn` is a type abbreviation, so `∈` targets the
`Lp F p (μ.restrict Ω)` subgroup, not the coerced type). -/

/-- The bundled norm is the `ℝ≥0∞` seminorm made real: the `ℝ≥0∞ → ℝ` off-ramp. -/
theorem norm_toLpOn [Fact (1 ≤ p)] {f : E → F} (h : MemLpOn Ω μ p f) :
    ‖h.toLpOn‖ = (eLpNormOn Ω μ p f).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae h.coeFn_toLpOn]
  rfl

/-- Sanity check: `L²(Ω)` with complex-vector codomain is a complex Hilbert space (and complete). -/
example {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} : True := by
  have : InnerProductSpace ℂ (LpOn Ω volume 2 (EuclideanSpace ℂ (Fin d))) := inferInstance
  have : CompleteSpace (LpOn Ω volume 2 (EuclideanSpace ℂ (Fin d))) := inferInstance
  trivial

end PDETheory
