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
public import PrimeCarleson.Frozen.Exp

/-!
# Frozen: `PrimeCarleson.modulatedSum`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The modulated singular sum `∑_{n ≠ 0} f(x - n) w(|n|) e(λ n) / n` for a weight
`w : ℕ → ℝ` (the sums in (e:Carweight), (e:CP) and the Appendix A.1 lemma). The sum has
finitely many nonzero terms because `f` is finitely supported. -/
def modulatedSum (w : ℕ → ℝ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else f (x - n) * (w n.natAbs : ℂ) * e (lam * n) / (n : ℂ)

end PrimeCarleson
