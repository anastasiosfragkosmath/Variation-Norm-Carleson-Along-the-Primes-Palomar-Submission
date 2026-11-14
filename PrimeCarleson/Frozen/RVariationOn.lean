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
# Frozen: `PrimeCarleson.rVariationOn`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson

/-- The `r`-variation of a family `(a_λ)` over an index set `S ⊆ ℝ`: the supremum over finite
increasing sequences `λ₀ < ⋯ < λ_J` in `S` of `(∑ᵢ |a_{λᵢ} - a_{λᵢ₊₁}|^r)^{1/r}`
([O+] (1.1), with the index set `ℕ₀` replaced by `S`; [O+] uses `S = ℝ`, transference a
finite `S`). Only `0 < r` has source meaning. -/
def rVariationOn (r : ℝ) (S : Set ℝ) (a : ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (t : Fin (J + 1) → ℝ) (_ : StrictMono t) (_ : ∀ i, t i ∈ S),
    (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r)

end PrimeCarleson
