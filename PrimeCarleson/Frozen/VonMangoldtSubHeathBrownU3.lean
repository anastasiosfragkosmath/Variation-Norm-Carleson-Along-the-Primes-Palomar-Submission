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
public import PrimeCarleson.Frozen.HeathBrownModel
import PrimeCarleson.Proof.VonMangoldtSubHeathBrownU3

/-!
# Frozen: `PrimeCarleson.vonMangoldt_sub_heathBrown_U3`

The statement as the author approved it before any proof was written; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- **[F+] Proposition 3.1.** With `Q_N = exp((log N)^{1/10})`, for every `A ≥ 1` there is
`C_A` with `‖Λ - Λ_{≤ Q_N}‖_{U³[N]} ≤ C_A (log N)^{-A}`. The source says `N ≥ 1`; at `N = 1`
the right side `(log 1)^{-A}` is infinite, so the content is `N ≥ 2`. -/
theorem vonMangoldt_sub_heathBrown_U3 :
    ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ N : ℕ+, 2 ≤ N →
      gowersNormInterval 3 N
          (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
            heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤
        C * Real.log N ^ (-A) :=
  by exact PrimeCarleson.Proof.vonMangoldt_sub_heathBrown_U3

end PrimeCarleson
