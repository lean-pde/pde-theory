import PDETheory.Geometry.Domain.Basic

/-!
# Smooth and `Cᵏ` domains

Instantiating the boundary-graph core `PDETheory.HasBoundaryGraphOf` at the `Cᵏ` regularity classes
gives the smooth ladder of domains. The smoothness order is `WithTop ℕ∞` (`ContDiff` scope): a
natural number `k`, `∞` for `C^∞`, or `ω` for analytic.

* `PDETheory.HasCkBoundary k Ω` / `PDETheory.IsCkDomain k Ω`;
* `PDETheory.IsC1Domain`, `PDETheory.IsSmoothDomain`, `PDETheory.IsAnalyticDomain` as the standard
  instances.

The bridge from `Cᵏ` (`k ≥ 1`) boundaries to `IsLipschitzDomain`, which requires a uniform Lipschitz
constant on compact boundaries, is deferred to a later phase.
-/

open scoped RealInnerProductSpace ContDiff

namespace PDETheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Set E}

/-- The boundary of `Ω` is locally the graph of a `Cᵏ` function. -/
def HasCkBoundary (k : WithTop ℕ∞) (Ω : Set E) : Prop :=
  HasBoundaryGraphOf (fun φ => ContDiff ℝ k φ) Ω

/-- `Ω` is a `Cᵏ` domain: open, with a locally `Cᵏ`-graph boundary. -/
def IsCkDomain (k : WithTop ℕ∞) (Ω : Set E) : Prop :=
  IsOpen Ω ∧ HasCkBoundary k Ω

/-- A `C¹` domain. -/
abbrev IsC1Domain (Ω : Set E) : Prop := IsCkDomain 1 Ω

/-- A smooth (`C^∞`) domain. -/
abbrev IsSmoothDomain (Ω : Set E) : Prop := IsCkDomain ∞ Ω

/-- An analytic (`C^ω`) domain. -/
abbrev IsAnalyticDomain (Ω : Set E) : Prop := IsCkDomain ω Ω

lemma IsCkDomain.isOpen {k : WithTop ℕ∞} (h : IsCkDomain k Ω) : IsOpen Ω := h.1

lemma hasCkBoundary_iff {k : WithTop ℕ∞} :
    HasCkBoundary k Ω ↔ HasBoundaryGraphOf (fun φ => ContDiff ℝ k φ) Ω := Iff.rfl

/-- **Regularity ladder.** A higher-order `Cᵏ` boundary is also a lower-order one. -/
lemma HasCkBoundary.mono {k l : WithTop ℕ∞} (hlk : l ≤ k) (h : HasCkBoundary k Ω) :
    HasCkBoundary l Ω :=
  HasBoundaryGraphOf.mono_pred (fun _ hφ => hφ.of_le hlk) h

lemma IsCkDomain.mono {k l : WithTop ℕ∞} (hlk : l ≤ k) (h : IsCkDomain k Ω) :
    IsCkDomain l Ω :=
  ⟨h.1, h.2.mono hlk⟩

end PDETheory
