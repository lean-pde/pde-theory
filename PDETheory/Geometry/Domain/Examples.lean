import PDETheory.Geometry.Domain.Lipschitz
import PDETheory.Geometry.Domain.Smooth

/-!
# Worked examples

The open half-space `{x | 0 < ⟪x, ν⟫}`, written as the strict epigraph of the zero function over
the hyperplane `ν^⟂`, is simultaneously

* an `IsSpecialLipschitzDomain` (a single global Lipschitz graph),
* an `IsLipschitzDomain` (via `IsSpecialLipschitzDomain.isLipschitzDomain`), and
* an `IsSmoothDomain`.

These serve as correctness tests: each statement elaborates only if the definitions are right.
-/

open scoped RealInnerProductSpace ContDiff
open Set

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The half-space is a special Lipschitz domain. -/
example {ν : E} (hν : ‖ν‖ = 1) :
    IsSpecialLipschitzDomain (strictEpigraph 0 ν (fun _ => (0 : ℝ))) :=
  ⟨ν, fun _ => 0, 0, hν, LipschitzWith.const 0, rfl⟩

/-- The half-space is a Lipschitz domain. -/
example {ν : E} (hν : ‖ν‖ = 1) :
    IsLipschitzDomain (strictEpigraph 0 ν (fun _ => (0 : ℝ))) :=
  IsSpecialLipschitzDomain.isLipschitzDomain ⟨ν, fun _ => 0, 0, hν, LipschitzWith.const 0, rfl⟩

/-- The half-space is a smooth domain. -/
example {ν : E} (hν : ‖ν‖ = 1) :
    IsSmoothDomain (strictEpigraph 0 ν (fun _ => (0 : ℝ))) := by
  refine ⟨isOpen_strictEpigraph continuous_const 0 ν, ?_⟩
  intro z hz
  have hzν : ⟪z, ν⟫ = 0 := by
    have hfr := frontier_strictEpigraph (φ := fun _ : E => (0 : ℝ)) continuous_const hν 0
    rw [hfr] at hz
    simp only [graphSet, mem_ofPred_eq, sub_zero] at hz
    exact hz.symm
  refine ⟨ν, fun _ => 0, 1, 1, hν, one_pos, one_pos, contDiff_const, ?_, ?_⟩
  · intro y _ _; show |(0 : ℝ)| < 1; norm_num
  · have hset : strictEpigraph z ν (fun _ => (0 : ℝ)) = strictEpigraph 0 ν (fun _ => (0 : ℝ)) := by
      ext x
      simp only [strictEpigraph, mem_ofPred_eq, sub_zero, inner_sub_left, hzν]
    rw [hset]

end PDETheory
