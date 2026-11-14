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
public import PrimeCarleson.Frozen.PeriodicBlockMax
import PrimeCarleson.Proof.PeriodicBlockMaxBound

/-!
# Frozen: `PrimeCarleson.periodicBlockMax_bound`

The statement as the author approved it before any proof was written; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- **Proposition `p:goal0`** (with an explicit constant). For
`κ = 1/D₀ - ε` small enough (`D₀` large) and `0 < ε ≤ κ/100` (e:epskappa), and every comparability
constant `A` in `|B| ≈ Q^κ` (e:kappa), there is `C` such that for every dyadic `Q = 2^j` and every
set `B` of squarefree integers in `(Q/2, Q]` with `Q^κ ≤ A |B|` and `|B| ≤ A Q^κ`, the operator norm
`𝔪_B` of `M_B` on `L²(ℤ/N)` is at most `C Q^{κ-1-ε}`; stated as
`∑_{x ∈ ℤ/N} M_B f(x)² ≤ (C Q^{κ-1-ε})² ∑_{x ∈ ℤ/N} |f(x)|²` (normalizations cancel). -/
theorem periodicBlockMax_bound :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ε : ℝ, 0 < ε → ε ≤ κ / 100 →
      ∀ A : ℝ, ∃ C : ℝ, ∀ (j : ℕ) (B : Finset ℕ),
        B ⊆ (Finset.Ioc (2 ^ j / 2) (2 ^ j)).filter Squarefree →
        ((2 : ℝ) ^ j) ^ κ ≤ A * B.card → (B.card : ℝ) ≤ A * ((2 : ℝ) ^ j) ^ κ →
        ∀ f : ℤ → ℂ, Function.Periodic f ((B.lcm id : ℕ) : ℤ) →
          ∑ x ∈ Finset.range (B.lcm id), periodicBlockMax B f x ^ 2 ≤
            (C * ((2 : ℝ) ^ j) ^ (κ - 1 - ε)) ^ 2 *
              ∑ x ∈ Finset.range (B.lcm id), ‖f x‖ ^ 2 :=
  by exact PrimeCarleson.Proof.periodicBlockMax_bound

end PrimeCarleson
