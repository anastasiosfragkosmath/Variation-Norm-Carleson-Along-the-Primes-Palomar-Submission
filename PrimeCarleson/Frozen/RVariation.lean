module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Order.LiminfLimsup

/-!
# Frozen: `PrimeCarleson.rVariation`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- The `r`-variation of a family `(a_λ)` indexed by `λ ∈ 𝕋 = [0, 1)` (line 250, with the
order on `[0, 1)`): the supremum over finite increasing sequences `λ₀ < ⋯ < λ_J` in `[0, 1)` of
`(∑ᵢ |a_{λᵢ} - a_{λᵢ₊₁}|^r)^{1/r}`. Only `0 < r` has source meaning; no statement uses
`r ≤ 0`. -/
def rVariation (r : ℝ) (a : ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (t : Fin (J + 1) → ℝ) (_ : StrictMono t) (_ : ∀ i, t i ∈ Set.Ico (0 : ℝ) 1),
    (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r)

end PrimeCarleson
