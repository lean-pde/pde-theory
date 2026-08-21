import PDETheory.Analysis.Sobolev.MemWkp

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

## Implementation notes

The `AEStronglyMeasurable` witnesses are bundled into the definition so that a member can later be
lifted to an element of the bundled `Lᵖ`-based Hilbert space without re-choosing representatives.
The theorem `W^{1,p}₀(Ω) ⊆ W^{1,p}(Ω)` (for `1 ≤ p`) is developed separately.
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

end PDETheory
