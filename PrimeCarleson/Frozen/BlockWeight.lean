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
public import PrimeCarleson.Frozen.RamanujanSum

/-!
# Frozen: `PrimeCarleson.blockWeight`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- `w_{Q,B}(n) = ∑_{q ∈ B} μ(q)/φ(q) · c_q(n)` (L605–L607). With `B = (Q/2, Q] ∩ ℕ` this is
`w_Q(n)` of (e:WQ) and the Heath-Brown slice `Λ_Q(n)` of [F+] (e:lambdaQ), L333. -/
def blockWeight (B : Finset ℕ) (n : ℤ) : ℂ :=
  ∑ q ∈ B, (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) * ramanujanSum q n

end PrimeCarleson
