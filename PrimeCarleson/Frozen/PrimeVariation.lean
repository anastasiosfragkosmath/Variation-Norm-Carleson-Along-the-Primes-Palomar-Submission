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
public import PrimeCarleson.Frozen.RVariation
public import PrimeCarleson.Frozen.ModulatedSum

/-!
# Frozen: `PrimeCarleson.primeVariation`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The variation-norm prime Carleson operator `𝒱^r_ℙ f(x)` of (e:Carweight), with
`w(n) = Λ(|n|)` (e:wweight). -/
def primeVariation (r : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) : ℝ≥0∞ :=
  rVariation r (fun lam => modulatedSum (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f lam x)

end PrimeCarleson
