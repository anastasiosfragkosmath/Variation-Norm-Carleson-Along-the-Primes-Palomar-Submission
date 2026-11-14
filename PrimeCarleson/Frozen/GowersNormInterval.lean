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
public import PrimeCarleson.Frozen.GowersNorm
public import PrimeCarleson.Frozen.RestrictInterval

/-!
# Frozen: `PrimeCarleson.gowersNormInterval`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The normalized Gowers norm `‖g‖_{U^s([N])} = ‖g 1_{[N]}‖_{U^s(ℤ)} / ‖1_{[N]}‖_{U^s(ℤ)}`
(line 706). -/
def gowersNormInterval (s : ℕ+) (N : ℕ+) (g : ℤ → ℂ) : ℝ :=
  gowersNorm s (restrictInterval N g) / gowersNorm s (restrictInterval N 1)

end PrimeCarleson
