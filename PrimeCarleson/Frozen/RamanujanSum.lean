module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Ring.Periodic
public import PrimeCarleson.Frozen.Exp
public import PrimeCarleson.Frozen.GowersNormInterval

/-!
# Frozen: `PrimeCarleson.ramanujanSum`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- The Ramanujan sum `c_q(n) = ∑_{1 ≤ a ≤ q, (a, q) = 1} e(a n / q)` ((e:ram) L587–L589;
[F+] (e:lambdaQ) L333–L335, where [F+] prints the summand without `n`). -/
def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q), e ((a : ℝ) * n / q)

end PrimeCarleson
