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
public import PrimeCarleson.Frozen.BlockWeight

/-!
# Frozen: `PrimeCarleson.heathBrownModel`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- The Heath-Brown model `Λ_{≤T} = ∑_{Q ≤ T, Q dyadic} Λ_Q` ([F+] (e:lambda000), L338–L341),
with dyadic `Q = 2^j`, `j ≥ 0`, and `(Q/2, Q] ∩ ℕ = Ioc (2^j / 2) (2^j)` (natural-number
division). Every `j` with `2^j ≤ T` has `j ≤ ⌊T⌋₊`, so the range below contains all of them. -/
def heathBrownModel (T : ℝ) (n : ℤ) : ℂ :=
  ∑ j ∈ (Finset.range (⌊T⌋₊ + 1)).filter (fun j => (2 : ℝ) ^ j ≤ T),
    blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j)) n

end PrimeCarleson
