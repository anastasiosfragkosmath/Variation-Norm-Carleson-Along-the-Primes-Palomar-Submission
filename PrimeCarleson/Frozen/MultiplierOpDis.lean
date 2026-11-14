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
# Frozen: `PrimeCarleson.multiplierOpDis`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- The discrete operator of [MSW] §2: `T_dis f = f ⋆ K|_ℤ`, i.e.
`T_dis f(n) = ∑_k f(k) K(n - k)` with `K(x) = ∫ m(ξ) e^{2πixξ} dξ`. -/
def multiplierOpDis (m : ℝ → ℂ) (f : ℤ →₀ ℂ) (n : ℤ) : ℂ :=
  f.sum fun k c => c * ∫ ξ, m ξ * e (((n - k : ℤ) : ℝ) * ξ)

end PrimeCarleson
