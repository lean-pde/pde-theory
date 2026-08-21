import Mathlib

/-!
# Test functions and test fields

The building block of the weak (distributional) theory on a domain `Ω`: a **test field** is a smooth,
compactly-supported function whose support sits inside `Ω`. Integration by parts against such
functions never produces boundary terms (the support avoids `∂Ω`), so a test field encodes the
"vanishing at the boundary" needed to define weak derivatives and the zero-trace space `W^{1,p}₀`.

We use a lightweight predicate rather than mathlib's bundled `𝓓(Ω, F)` (`TestFunction`): the latter
requires `Ω : TopologicalSpace.Opens E` and carries an LF topology that is dead weight for the
integral manipulations here, whereas the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) is stated in exactly the raw
`ContDiff ∞ ∧ HasCompactSupport ∧ tsupport ⊆ Ω` form. (A bridge from `𝓓` can be added later for
upstreaming.)

## Main definitions

* `PDETheory.IsTestField Ω φ` : `φ : E → F` is a smooth compactly-supported field with `tsupport ⊆ Ω`.
* `PDETheory.IsTestFn Ω ψ` : the scalar (`F = ℝ`) case, used as the test object for weak derivatives.

## Main results

Structural closure (`add`, `neg`, `sub`, `smul`, `mono`) and the analytic facts a test field enjoys:
continuity, membership in every `Lᵖ`, integrability, and local integrability.
-/

open scoped ContDiff ENNReal NNReal
open MeasureTheory

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `φ : E → F` is a **test field** on `Ω`: smooth, compactly supported, with support inside `Ω`. -/
def IsTestField (Ω : Set E) (φ : E → F) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- A scalar (`ℝ`-valued) **test function** on `Ω`: the object weak derivatives are tested against. -/
abbrev IsTestFn (Ω : Set E) (ψ : E → ℝ) : Prop := IsTestField Ω ψ

namespace IsTestField

variable {Ω : Set E} {φ ψ : E → F}

lemma contDiff (h : IsTestField Ω φ) : ContDiff ℝ ∞ φ := h.1
lemma hasCompactSupport (h : IsTestField Ω φ) : HasCompactSupport φ := h.2.1
lemma tsupport_subset (h : IsTestField Ω φ) : tsupport φ ⊆ Ω := h.2.2

lemma continuous (h : IsTestField Ω φ) : Continuous φ := h.contDiff.continuous

/-- Enlarging the domain preserves the test-field property. -/
lemma mono {Ω' : Set E} (hΩ : Ω ⊆ Ω') (h : IsTestField Ω φ) : IsTestField Ω' φ :=
  ⟨h.contDiff, h.hasCompactSupport, h.tsupport_subset.trans hΩ⟩

lemma add (h : IsTestField Ω φ) (h' : IsTestField Ω ψ) : IsTestField Ω (φ + ψ) := by
  refine ⟨h.contDiff.add h'.contDiff, h.hasCompactSupport.add h'.hasCompactSupport, ?_⟩
  have hsub : Function.support (φ + ψ) ⊆ Function.support φ ∪ Function.support ψ := by
    intro x hx
    simp only [Function.mem_support, Pi.add_apply, Set.mem_union] at hx ⊢
    by_contra hc
    push_neg at hc
    exact hx (by rw [hc.1, hc.2, add_zero])
  refine (closure_mono hsub).trans ?_
  rw [closure_union]
  exact Set.union_subset h.tsupport_subset h'.tsupport_subset

lemma neg (h : IsTestField Ω φ) : IsTestField Ω (-φ) := by
  refine ⟨h.contDiff.neg, h.hasCompactSupport.neg, ?_⟩
  have hsub : Function.support (-φ) ⊆ Function.support φ := by
    intro x hx
    simp only [Function.mem_support, Pi.neg_apply, ne_eq, neg_eq_zero] at hx ⊢
    exact hx
  exact (closure_mono hsub).trans h.tsupport_subset

lemma sub (h : IsTestField Ω φ) (h' : IsTestField Ω ψ) : IsTestField Ω (φ - ψ) := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

lemma smul (c : ℝ) (h : IsTestField Ω φ) : IsTestField Ω (c • φ) := by
  have hsub : Function.support (c • φ) ⊆ Function.support φ := by
    intro x hx
    simp only [Function.mem_support, Pi.smul_apply, ne_eq] at hx ⊢
    exact fun h0 => hx (by rw [h0, smul_zero])
  have htsub : tsupport (c • φ) ⊆ tsupport φ := closure_mono hsub
  exact ⟨h.contDiff.const_smul c,
    IsCompact.of_isClosed_subset h.hasCompactSupport isClosed_closure htsub,
    htsub.trans h.tsupport_subset⟩

/-! ### Analytic consequences -/

section Measure
variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma memLp (h : IsTestField Ω φ) [IsFiniteMeasureOnCompacts μ] (p : ℝ≥0∞) : MemLp φ p μ :=
  h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport

lemma integrable (h : IsTestField Ω φ) [IsFiniteMeasureOnCompacts μ] : Integrable φ μ :=
  h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport

lemma locallyIntegrable (h : IsTestField Ω φ) [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ] :
    LocallyIntegrable φ μ :=
  h.continuous.locallyIntegrable

end Measure

end IsTestField

end PDETheory
