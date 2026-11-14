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
# Frozen: `PrimeCarleson.periodicBlockMax`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- The periodic maximal operator of the paper (L2117–L2120):
`M_B f(x) = sup_{θ ∈ ℤ/N} |𝔼_{r ∈ ℤ/N} f(x - r) w_{Q,B}(r) e_N(r θ)|` with
`N = 𝒬_B = lcm(B)`, for `N`-periodic `f : ℤ → ℂ` (residues mod `N` represented by
`0, …, N - 1`; `w_{Q,B}` and `e_N(r θ)` are `N`-periodic in `r` and `θ`). -/
def periodicBlockMax (B : Finset ℕ) (f : ℤ → ℂ) (x : ℤ) : ℝ :=
  ⨆ θ : Fin (B.lcm id),
    ‖((B.lcm id : ℕ) : ℂ)⁻¹ * ∑ r : Fin (B.lcm id),
        f (x - (r : ℕ)) * blockWeight B (r : ℕ) *
          e (((r : ℕ) : ℝ) * ((θ : ℕ) : ℝ) / ((B.lcm id : ℕ) : ℝ))‖

end PrimeCarleson
