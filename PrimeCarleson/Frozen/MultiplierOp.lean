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
# Frozen: `PrimeCarleson.multiplierOp`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- The Fourier multiplier operator on `ℝ` with multiplier `m`, on Schwartz functions
([MSW] §2): `(T F)(x) = ∫ m(ξ) F̂(ξ) e^{2πiξx} dξ`. -/
def multiplierOp (m : ℝ → ℂ) (F : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∫ ξ, m ξ * (∫ y, F y * e (-(y * ξ))) * e (ξ * x)

end PrimeCarleson
