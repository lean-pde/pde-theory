import PDETheory.Analysis.Sobolev.LpOn
import PDETheory.Analysis.Sobolev.MemW1p0
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The bundled `H¹₀(Ω)` Hilbert space (coordinate model)

`MemW1p0`/`MemH10` are predicate-level. Operator theory (Lax–Milgram, spectral methods, the Stokes
problem) needs a genuine **bundled Hilbert space**. The coordinate-free weak gradient is
`(E →L[ℝ] F)`-valued, but the operator-norm space `E →L[ℝ] F` carries **no `InnerProductSpace`
instance** (its norm is not induced by an inner product). So the bundled `H¹₀` stores the
**Hilbert–Schmidt / coordinate Jacobian** fiber `PiLp 2 (fun _ : Fin d => 𝕜^m)`, which *is* an
inner-product space — mathematically the right object, since the `H¹` inner product is
`∫⟪u,v⟫ + ∑ᵢ ∫⟪∂ᵢu, ∂ᵢv⟫`, the HS pairing. Consequently the bundled layer lives in the coordinate
model (`EuclideanSpace`).

The space is the closure of the test-field graphs `(φ, ∇φ)` inside the product Hilbert space
`L²(Ω; 𝕜^m) ⊕ L²(Ω; HS-Jacobian)`.

## Main definitions

* `PDETheory.Dom d` / `PDETheory.Cod 𝕜 m` : the coordinate models `ℝ^d` and `𝕜^m`.
* `PDETheory.GradFib 𝕜 d m` : the Hilbert–Schmidt Jacobian fiber `PiLp 2 (fun _ : Fin d => 𝕜^m)`.
* `PDETheory.gradPi φ` : the coordinate Jacobian `x ↦ (∂ᵢφ(x))ᵢ`.
* `PDETheory.H1Product Ω μ 𝕜 m` : the product Hilbert space `L²(Ω; 𝕜^m) ⊕ L²(Ω; GradFib)`.
* `PDETheory.testFieldGraph Ω μ 𝕜 m` : the `𝕜`-span of the graphs `(φ, gradPi φ)` of test fields.
* `PDETheory.H10Space Ω μ 𝕜 m` : the topological closure of `testFieldGraph` — the bundled `H¹₀(Ω)`.

## Main results

* `↥(H10Space Ω μ 𝕜 m)` is a `𝕜`-Hilbert space: `InnerProductSpace 𝕜` and `CompleteSpace`, inherited
  from the closed subspace of the product Hilbert space (over `ℂ` in particular, for Stokes).

## Implementation notes

The predicate/bundled bridge `MemH10 Ω μ u ↔ ∃ w : ↥(H10Space Ω μ ℂ m), …` is **deferred**: it needs
the operator-norm ↔ Hilbert–Schmidt norm equivalence on `ℝ^d →L[ℝ] 𝕜^m ≅ GradFib` together with
a.e.-class plumbing. This file provides the bundled space itself, the foundation for the
operator-theoretic layer.
-/

open scoped ENNReal
open MeasureTheory

namespace PDETheory

variable {d m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- Domain model `ℝ^d`. -/
abbrev Dom (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Codomain model `𝕜^m`. -/
abbrev Cod (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) := EuclideanSpace 𝕜 (Fin m)

/-- The Hilbert–Schmidt Jacobian fiber: `𝕜^m`-tuples indexed by the `d` coordinate directions, with
the `ℓ²` (Hilbert–Schmidt) norm. -/
abbrev GradFib (𝕜 : Type*) [RCLike 𝕜] (d m : ℕ) := PiLp 2 (fun _ : Fin d => Cod 𝕜 m)

/-- The **assembly** map `A ↦ (A eᵢ)ᵢ` sending a linear map `ℝ^d →L 𝕜^m` to its coordinate Jacobian
in the Hilbert–Schmidt fiber. -/
noncomputable def gradAssembly (A : Dom d →L[ℝ] Cod 𝕜 m) : GradFib 𝕜 d m :=
  WithLp.toLp 2 (fun i => A (EuclideanSpace.single i (1 : ℝ)))

theorem continuous_gradAssembly :
    Continuous (gradAssembly : (Dom d →L[ℝ] Cod 𝕜 m) → GradFib 𝕜 d m) := by
  unfold gradAssembly; fun_prop

@[simp] theorem gradAssembly_zero : gradAssembly (0 : Dom d →L[ℝ] Cod 𝕜 m) = 0 := by
  simp only [gradAssembly, zero_apply]; rfl

/-- The **coordinate Jacobian** of `φ : ℝ^d → 𝕜^m` at `x`: the tuple `(∂ᵢφ(x))ᵢ` of directional
derivatives along the coordinate axes, assembled in the Hilbert–Schmidt fiber `GradFib`. -/
noncomputable def gradPi (φ : Dom d → Cod 𝕜 m) (x : Dom d) : GradFib 𝕜 d m :=
  gradAssembly (fderiv ℝ φ x)

/-- The coordinate Jacobian of a test field is continuous. -/
theorem continuous_gradPi {Ω : Set (Dom d)} {φ : Dom d → Cod 𝕜 m} (hφ : IsTestField Ω φ) :
    Continuous (gradPi φ) :=
  continuous_gradAssembly.comp (hφ.contDiff.continuous_fderiv (by simp))

/-- The coordinate Jacobian of a test field is compactly supported (it vanishes off `tsupport φ`). -/
theorem hasCompactSupport_gradPi {Ω : Set (Dom d)} {φ : Dom d → Cod 𝕜 m} (hφ : IsTestField Ω φ) :
    HasCompactSupport (gradPi φ) :=
  (hφ.hasCompactSupport.fderiv ℝ).comp_left gradAssembly_zero

/-- A test field lies in `L²(Ω)`. -/
theorem memLpOn_isTestField {Ω : Set (Dom d)} {μ : Measure (Dom d)} [μ.IsAddHaarMeasure]
    {φ : Dom d → Cod 𝕜 m} (hφ : IsTestField Ω φ) : MemLpOn Ω μ 2 φ :=
  (hφ.memLp 2).restrict Ω

/-- The coordinate Jacobian of a test field lies in `L²(Ω)`. -/
theorem memLpOn_gradPi {Ω : Set (Dom d)} {μ : Measure (Dom d)} [μ.IsAddHaarMeasure]
    {φ : Dom d → Cod 𝕜 m} (hφ : IsTestField Ω φ) : MemLpOn Ω μ 2 (gradPi φ) :=
  ((continuous_gradPi hφ).memLp_of_hasCompactSupport (hasCompactSupport_gradPi hφ)).restrict Ω

/-- The `H¹` product Hilbert space `L²(Ω; 𝕜^m) ⊕ L²(Ω; GradFib)` (with the `WithLp 2` product norm).
It is a `𝕜`-Hilbert space; `H10Space` will be a closed subspace of it. -/
abbrev H1Product (Ω : Set (Dom d)) (μ : Measure (Dom d)) (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) : Type _ :=
  WithLp 2 (LpOn Ω μ 2 (Cod 𝕜 m) × LpOn Ω μ 2 (GradFib 𝕜 d m))

/-- The graph `(φ, gradPi φ)` of a test field, as an element of the product Hilbert space. -/
noncomputable def testFieldGraphElem {Ω : Set (Dom d)} {μ : Measure (Dom d)} [μ.IsAddHaarMeasure]
    {φ : Dom d → Cod 𝕜 m} (hφ : IsTestField Ω φ) : H1Product Ω μ 𝕜 m :=
  WithLp.toLp 2 ((memLpOn_isTestField hφ).toLpOn, (memLpOn_gradPi hφ).toLpOn)

/-- The `𝕜`-linear span of the test-field graphs `(φ, gradPi φ)` inside the product Hilbert space. -/
noncomputable def testFieldGraph (Ω : Set (Dom d)) (μ : Measure (Dom d)) [μ.IsAddHaarMeasure]
    (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) : Submodule 𝕜 (H1Product Ω μ 𝕜 m) :=
  Submodule.span 𝕜 { w | ∃ (φ : Dom d → Cod 𝕜 m) (hφ : IsTestField Ω φ), w = testFieldGraphElem hφ }

/-- The bundled **`H¹₀(Ω)`**: the topological closure of the test-field graphs in the product
Hilbert space. Its coercion `↥(H10Space …)` is a `𝕜`-Hilbert space. -/
noncomputable def H10Space (Ω : Set (Dom d)) (μ : Measure (Dom d)) [μ.IsAddHaarMeasure]
    (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) : Submodule 𝕜 (H1Product Ω μ 𝕜 m) :=
  (testFieldGraph Ω μ 𝕜 m).topologicalClosure

/-- `H¹₀(Ω)` is a complete space (closed subspace of the complete product Hilbert space). -/
noncomputable instance instCompleteSpaceH10 (Ω : Set (Dom d)) (μ : Measure (Dom d))
    [μ.IsAddHaarMeasure] (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) : CompleteSpace ↥(H10Space Ω μ 𝕜 m) :=
  inferInstanceAs (CompleteSpace ↥((testFieldGraph Ω μ 𝕜 m).topologicalClosure))

/-- **`H¹₀(Ω)` is a complex Hilbert space** (the genuine object for the Stokes application):
`↥(H10Space Ω volume ℂ m)` carries an `InnerProductSpace ℂ` (from the closed subspace of the product
Hilbert space) and is a `CompleteSpace`. -/
example {d m : ℕ} {Ω : Set (Dom d)} : True := by
  have : InnerProductSpace ℂ ↥(H10Space Ω volume ℂ m) := inferInstance
  have : CompleteSpace ↥(H10Space Ω volume ℂ m) := inferInstance
  trivial

end PDETheory
