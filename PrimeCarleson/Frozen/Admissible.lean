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
public import PrimeCarleson.Frozen.GowersNormInterval
public import PrimeCarleson.Frozen.MajorArcModel

/-!
# Frozen: `PrimeCarleson.Admissible`

The definition as the author approved it before any proof used it; it is the only
declaration in this file.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- A weight `w ≥ 0` is *admissible* (Appendix A.1), with the `o(1)` terms read as
follows: `q^{o(1)-1}` as `C_ε q^{ε-1}` for every `ε > 0`, and `M(N) ≤ N^{o(1)}` as
`M(N) ≤ C_ε N^ε` for every `ε > 0`.

* Upper normalization: some `0 < C < ∞` bounds, for every `0 ≤ C₀ < ∞`,
  `limsup_{N → ∞} (1/N) ∑_{n ∈ (C₀N, C₀N + N]} w(n)`.
* Heath-Brown-type approximation: there are `C < ∞`, `S : ℚ → ℂ` with
  `|S(a/q)| ≤ C_ε q^{ε-1}`, `ν > 4`, `s ≥ 3` and a truncation `M(N) ≤ C_ε N^ε` such that
  for all sufficiently large `N`,
  `‖w - ∑_{q ≤ M(N)} ∑_{(a,q)=1} S(a/q) e(· a/q)‖_{U^s([N])} ≤ C log^{-ν/2^s} N`. -/
def Admissible (w : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ w n) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ C₀ : ℝ, 0 ≤ C₀ →
    limsup (fun N : ℕ => ENNReal.ofReal ((N : ℝ)⁻¹ *
      ∑ n ∈ Finset.Ioc ⌊C₀ * N⌋₊ ⌊C₀ * N + N⌋₊, w n)) atTop ≤ ENNReal.ofReal C) ∧
  (∃ C : ℝ, ∃ S : ℚ → ℂ,
    (∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ x : ℚ, ‖S x‖ ≤ Cε * (x.den : ℝ) ^ (ε - 1)) ∧
    ∃ ν : ℝ, 4 < ν ∧ ∃ s : ℕ+, 3 ≤ s ∧
    ∃ M : ℕ+ → ℕ, (∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ N : ℕ+, (M N : ℝ) ≤ Cε * (N : ℝ) ^ ε) ∧
    ∀ᶠ N : ℕ+ in atTop,
      gowersNormInterval s N (fun n => (w n.toNat : ℂ) - majorArcModel S (M N) n) ≤
        C * Real.log N ^ (-ν / 2 ^ (s : ℕ)))

end PrimeCarleson
