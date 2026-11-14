module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Order.LiminfLimsup
public import PrimeCarleson.Frozen.MultDiff

/-!
# Frozen: `PrimeCarleson.gowersNorm`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The Gowers norm `‖f‖_{U^s(ℤ)}`, `s ≥ 1`, of a finitely supported `f` (e;GowersDef):
the `2^s`-th root of `∑_{x, h₁, …, h_s} Δ_{h₁,…,h_s} f(x)`. That sum is a nonnegative real
number (`gowersNorm_spec`); its real part is taken so that the root is real. -/
def gowersNorm (s : ℕ+) (f : ℤ →₀ ℂ) : ℝ :=
  (∑' p : ℤ × (Fin s → ℤ), multDiff s p.2 f p.1).re ^ ((1 : ℝ) / 2 ^ (s : ℕ))

end PrimeCarleson
