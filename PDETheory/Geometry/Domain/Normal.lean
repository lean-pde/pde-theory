import PDETheory.Geometry.Domain.SurfaceMeasure

/-!
# The outward unit normal of a Lipschitz graph

On the graph of `φ` over the hyperplane `ν^⟂`, wherever `φ` is differentiable its (horizontal)
gradient `g ∈ ν^⟂` determines an **outward unit normal**

`outwardNormal ν g = (g - ν) / √(1 + ‖g‖²)`.

For a merely Lipschitz `φ` this is defined only almost everywhere — precisely at the differentiability
points supplied by Rademacher's theorem (a coordinate-free normal on `∂Ω`, valid everywhere, would
require the rectifiability / approximate-tangent-plane theory that mathlib does not yet have). This
file develops the pointwise algebra of this vector and its a.e. existence.

## Main results

* `PDETheory.norm_outwardNormal` : it is a unit vector.
* `PDETheory.inner_outwardNormal_normal` : orientation — it points strictly to the `-ν` side, i.e.
  out of the strict epigraph.
* `PDETheory.inner_outwardNormal_tangent` : it is orthogonal to every tangent vector
  `w + ⟪g, w⟫ • ν` of the graph (`w ∈ ν^⟂`).
* `PDETheory.ae_differentiableAt_graph` : Rademacher — the graph function is differentiable a.e. on
  the hyperplane, so the outward normal exists a.e.
-/

open scoped RealInnerProductSpace NNReal MeasureTheory
open Set MeasureTheory

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The outward unit normal to the graph of `φ` at a point with horizontal gradient `g`
(with `g ⊥ ν`): the unit vector `(g - ν) / √(1 + ‖g‖²)`, pointing to the `-ν` side. -/
noncomputable def outwardNormal (ν g : E) : E := (Real.sqrt (1 + ‖g‖ ^ 2))⁻¹ • (g - ν)

omit [InnerProductSpace ℝ E] in
/-- The normalising factor `√(1 + ‖g‖²)` is positive. -/
lemma sqrt_one_add_norm_sq_pos (g : E) : 0 < Real.sqrt (1 + ‖g‖ ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

/-- Key identity: `‖g - ν‖² = ‖g‖² + 1` when `g ⊥ ν` and `‖ν‖ = 1`. -/
lemma norm_sub_sq_of_orthogonal {ν g : E} (hν : ‖ν‖ = 1) (hg : ⟪g, ν⟫ = 0) :
    ‖g - ν‖ ^ 2 = ‖g‖ ^ 2 + 1 := by
  rw [norm_sub_sq_real, hg, hν]; ring

/-- The outward normal is a unit vector. -/
theorem norm_outwardNormal {ν g : E} (hν : ‖ν‖ = 1) (hg : ⟪g, ν⟫ = 0) :
    ‖outwardNormal ν g‖ = 1 := by
  have hpos := sqrt_one_add_norm_sq_pos g
  have hnormsub : ‖g - ν‖ = Real.sqrt (1 + ‖g‖ ^ 2) := by
    rw [show (1 : ℝ) + ‖g‖ ^ 2 = ‖g‖ ^ 2 + 1 from by ring, ← norm_sub_sq_of_orthogonal hν hg,
      Real.sqrt_sq (norm_nonneg _)]
  rw [outwardNormal, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, hnormsub,
    inv_mul_cancel₀ (ne_of_gt hpos)]

/-- Orientation: the outward normal has strictly negative component along `ν`, so it points out of
the strict epigraph `{x | φ (baseProj ν (x-z)) < ⟪x-z, ν⟫}`. -/
theorem inner_outwardNormal_normal {ν g : E} (hν : ‖ν‖ = 1) (hg : ⟪g, ν⟫ = 0) :
    ⟪outwardNormal ν g, ν⟫ = -(Real.sqrt (1 + ‖g‖ ^ 2))⁻¹ := by
  rw [outwardNormal, real_inner_smul_left, inner_sub_left, hg, real_inner_self_eq_norm_sq, hν]
  ring

theorem inner_outwardNormal_normal_neg {ν g : E} (hν : ‖ν‖ = 1) (hg : ⟪g, ν⟫ = 0) :
    ⟪outwardNormal ν g, ν⟫ < 0 := by
  rw [inner_outwardNormal_normal hν hg]
  exact neg_neg_iff_pos.mpr (inv_pos.mpr (sqrt_one_add_norm_sq_pos g))

/-- The outward normal is orthogonal to every graph tangent vector `w + ⟪g, w⟫ • ν`, `w ∈ ν^⟂`.
These vectors span the tangent plane to the graph (they are the images of the hyperplane under the
derivative of the graph parametrisation). -/
theorem inner_outwardNormal_tangent {ν g : E} (hν : ‖ν‖ = 1) (hg : ⟪g, ν⟫ = 0) {w : E}
    (hw : ⟪w, ν⟫ = 0) : ⟪outwardNormal ν g, w + ⟪g, w⟫ • ν⟫ = 0 := by
  have hνw : ⟪ν, w⟫ = 0 := by rw [real_inner_comm]; exact hw
  rw [outwardNormal, real_inner_smul_left, inner_sub_left, inner_add_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hν, hg, hνw]
  ring

/-! ### A.e. existence via Rademacher -/

open Module in
/-- **Rademacher for the boundary graph.** The graph function `φ`, viewed on the hyperplane subspace
`(ℝ ∙ ν)ᗮ`, is differentiable almost everywhere with respect to the `(dim - 1)`-dimensional Hausdorff
(= Haar) measure of that subspace. At every such point the horizontal gradient exists, so the
`outwardNormal` is defined; the algebraic lemmas above then give a genuine outward unit normal a.e. -/
theorem ae_differentiableAt_graph [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : E) {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∀ᵐ u ∂(μH[(finrank ℝ ((ℝ ∙ ν)ᗮ : Submodule ℝ E) : ℝ)] :
        Measure ((ℝ ∙ ν)ᗮ : Submodule ℝ E)),
      DifferentiableAt ℝ (fun u : ((ℝ ∙ ν)ᗮ : Submodule ℝ E) => φ ↑u) u := by
  have hlip : LipschitzWith (K * 1) (fun u : ((ℝ ∙ ν)ᗮ : Submodule ℝ E) => φ ↑u) :=
    hφ.comp isometry_subtype_coe.lipschitz
  exact hlip.ae_differentiableAt

/-- Any element of `ν^⟂` is orthogonal to `ν`. -/
lemma inner_coe_orthogonal_normal (ν : E) (k : ((ℝ ∙ ν)ᗮ : Submodule ℝ E)) : ⟪(↑k : E), ν⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left.mp (SetLike.coe_mem k)

/-- The **outward unit normal field** of the graph of `φ`, in chart coordinates: at a base point
`u ∈ ν^⟂` it is `outwardNormal` applied to the horizontal gradient of `φ`. It is defined everywhere
(the gradient defaults to `0` off the differentiability set) and, by `ae_differentiableAt_graph`,
coincides with the genuine geometric normal almost everywhere. -/
noncomputable def graphNormal [FiniteDimensional ℝ E] (ν : E) (φ : E → ℝ)
    (u : ((ℝ ∙ ν)ᗮ : Submodule ℝ E)) : E :=
  outwardNormal ν ↑(gradient (fun v : ((ℝ ∙ ν)ᗮ : Submodule ℝ E) => φ ↑v) u)

/-- The chart-coordinate outward normal field is everywhere a unit vector. -/
theorem norm_graphNormal [FiniteDimensional ℝ E] {ν : E} (hν : ‖ν‖ = 1) (φ : E → ℝ)
    (u : ((ℝ ∙ ν)ᗮ : Submodule ℝ E)) : ‖graphNormal ν φ u‖ = 1 :=
  norm_outwardNormal hν (inner_coe_orthogonal_normal ν _)

/-- The chart-coordinate outward normal points strictly to the `-ν` side (out of the epigraph). -/
theorem inner_graphNormal_normal_neg [FiniteDimensional ℝ E] {ν : E} (hν : ‖ν‖ = 1) (φ : E → ℝ)
    (u : ((ℝ ∙ ν)ᗮ : Submodule ℝ E)) : ⟪graphNormal ν φ u, ν⟫ < 0 :=
  inner_outwardNormal_normal_neg hν (inner_coe_orthogonal_normal ν _)

/-! ### The bundled outward unit normal field

For a bare function `n : E → E` there is no guarantee that it is *any* kind of normal, which would
make a boundary flux `∫_{∂Ω} ⟪F, n⟫ dσ` meaningless. The structure below packages the
coordinate-free requirements that make it a genuine **outward unit normal field**: measurability (so
the flux is well defined), unit length on `∂Ω`, and a geometric outward-orientation condition.

Design note: `isOutward` fixes the *orientation* (which side of the boundary), coordinate-freely and
without any rectifiability theory, but it pins only the outward hemisphere — a cone of tilted unit
vectors satisfies it. The stronger requirement that `ν` equal the exact geometric normal `σ`-a.e.
(the transported chart normal `graphNormal`), which is what makes the divergence *identity* hold, is
deliberately kept out of this structure: it is chart-coupled and needs the boundary surface-integral
transport (or rectifiability). See `PDETheory.HasGaussGreen`. -/

section Bundled
variable [MeasurableSpace E]

/-- An **outward unit normal field** for `Ω`: a measurable field `E → E` that is a unit vector at
every boundary point and points geometrically outward there. -/
structure OutwardNormal (Ω : Set E) where
  /-- The underlying field; its values on `∂Ω` are what matter. -/
  toFun : E → E
  /-- Measurability, so the surface integral `∫_{∂Ω} ⟪F, ν⟫ dσ` is well defined. -/
  measurable' : Measurable toFun
  /-- `ν` is a unit vector at every boundary point. -/
  unit_of_mem_frontier : ∀ x ∈ frontier Ω, ‖toFun x‖ = 1
  /-- `ν` points outward: from a boundary point `x`, a small step along `+ν` leaves `closure Ω`
  and a small step along `-ν` enters `Ω`. This fixes the orientation coordinate-freely. -/
  isOutward : ∀ x ∈ frontier Ω, ∃ ε > 0, ∀ t ∈ Set.Ioo (0 : ℝ) ε,
    x + t • toFun x ∉ closure Ω ∧ x - t • toFun x ∈ Ω

namespace OutwardNormal

variable {Ω : Set E}

instance : CoeFun (OutwardNormal Ω) (fun _ => E → E) := ⟨toFun⟩

@[simp] lemma coe_mk (f h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : OutwardNormal Ω) = f := rfl

/-- The outward normal is measurable. -/
theorem measurable (ν : OutwardNormal Ω) : Measurable (ν : E → E) := ν.measurable'

/-- The outward normal is a unit vector on the boundary. -/
@[simp] theorem norm_eq_one_of_mem_frontier (ν : OutwardNormal Ω) {x : E}
    (hx : x ∈ frontier Ω) : ‖ν x‖ = 1 :=
  ν.unit_of_mem_frontier x hx

end OutwardNormal

end Bundled

end PDETheory
