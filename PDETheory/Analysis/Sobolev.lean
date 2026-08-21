import PDETheory.Analysis.Sobolev.TestFunction
import PDETheory.Analysis.Sobolev.WeakDeriv

/-!
# Sobolev spaces on domains

Aggregator for the theory of Sobolev spaces on a domain `Ω`, built on the coordinate-free weak
Fréchet derivative. Re-exports:

* `PDETheory.Analysis.Sobolev.TestFunction` — the test-field predicate `IsTestField` / `IsTestFn`
  (smooth, compactly supported, `tsupport ⊆ Ω`) and its structural and analytic properties.
* `PDETheory.Analysis.Sobolev.WeakDeriv` — the weak directional / Fréchet derivative
  (`IsWeakDerivDir`, `IsWeakDeriv`) and that a `C¹` field's classical derivative is its weak
  derivative (`contDiff_isWeakDeriv`).

Further modules (`W^{1,p}`/`H¹`, `W^{1,p}₀`/`H¹₀`, Poincaré/coercivity, …) are added as the
development proceeds.
-/
