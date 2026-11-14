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
# Frozen: `PrimeCarleson.partialFourierIntegral`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- The partial (inverse) Fourier integral of a Schwartz function ([O+] before Theorem 1.2):
`𝒮[f](ξ, x) = ∫_{-∞}^{ξ} f̂(η) e^{2πiηx} dη` with `f̂(η) = ∫ f(y) e^{-2πiyη} dy`. -/
def partialFourierIntegral (f : 𝓢(ℝ, ℂ)) (ξ x : ℝ) : ℂ :=
  ∫ η in Set.Iic ξ, (∫ y, f y * e (-(y * η))) * e (η * x)

end PrimeCarleson
