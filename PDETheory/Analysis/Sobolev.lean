import PDETheory.Analysis.Sobolev.TestFunction
import PDETheory.Analysis.Sobolev.WeakDeriv
import PDETheory.Analysis.Sobolev.MemWkp
import PDETheory.Analysis.Sobolev.MemW1p0
import PDETheory.Analysis.Sobolev.Poincare

/-!
# Sobolev spaces on domains

Aggregator for the theory of Sobolev spaces on a domain `Ω`, built on the coordinate-free weak
Fréchet derivative. Re-exports:

* `PDETheory.Analysis.Sobolev.TestFunction` — the test-field predicate `IsTestField` / `IsTestFn`
  (smooth, compactly supported, `tsupport ⊆ Ω`) and its structural and analytic properties.
* `PDETheory.Analysis.Sobolev.WeakDeriv` — the weak directional / Fréchet derivative
  (`IsWeakDerivDir`, `IsWeakDeriv`) and that a `C¹` field's classical derivative is its weak
  derivative (`contDiff_isWeakDeriv`).
* `PDETheory.Analysis.Sobolev.MemWkp` — `Lᵖ(Ω)` (`MemLpOn`), `W^{1,p}(Ω)` (`MemW1p`) and `H¹(Ω)`
  (`MemH1`), with `IsTestField.memW1p`.
* `PDETheory.Analysis.Sobolev.MemW1p0` — the zero-trace space `W^{1,p}₀(Ω)` (`MemW1p0`) / `H¹₀(Ω)`
  (`MemH10`), with `IsTestField.memW1p0`.
* `PDETheory.Analysis.Sobolev.Poincare` — the Poincaré inequality for test fields on a bounded
  domain (`poincare_testField`).
-/
