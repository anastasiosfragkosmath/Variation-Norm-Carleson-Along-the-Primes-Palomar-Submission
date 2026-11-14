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
# Statements: A Variation Norm Carleson Theorem Along the Primes

Source: Fragkos, Krause, Miheisi, Sun, *A Variation Norm Carleson Theorem Along the
Primes*, `sources/Variational_Carleson.tex`. Sequences are finitely supported
(footnote at line 288), so the input carrier is `ℤ →₀ ℂ`. Norms and the
`r`-variation take values in `[0, ∞]`.

This is the Comparator challenge for the paper's two main theorems, Theorem 1.3
(`t:main`) and the maximal bound `t:carmax`. The two `sorry`s below are the challenge's
holes; `Solution.lean` proves both statements. The definitions are those of the
development, under the same names.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson

/-- `e(t) = e^{2πit}` (line 552). -/
def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-! ## Variation and the Carleson-type operators (lines 249–327, 2854) -/

/-- The `r`-variation of a family `(a_λ)` indexed by `λ ∈ 𝕋 = [0, 1)` (line 250, with the
order on `[0, 1)`): the supremum over finite increasing sequences `λ₀ < ⋯ < λ_J` in `[0, 1)` of
`(∑ᵢ |a_{λᵢ} - a_{λᵢ₊₁}|^r)^{1/r}`. Only `0 < r` has source meaning; no statement uses
`r ≤ 0`. -/
def rVariation (r : ℝ) (a : ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (t : Fin (J + 1) → ℝ) (_ : StrictMono t) (_ : ∀ i, t i ∈ Set.Ico (0 : ℝ) 1),
    (∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ r) ^ (1 / r)

/-- The modulated singular sum `∑_{n ≠ 0} f(x - n) w(|n|) e(λ n) / n` for a weight
`w : ℕ → ℝ` (the sums in (e:Carweight), (e:CP) and the Appendix A.1 lemma). The sum has
finitely many nonzero terms because `f` is finitely supported. -/
def modulatedSum (w : ℕ → ℝ) (f : ℤ →₀ ℂ) (lam : ℝ) (x : ℤ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else f (x - n) * (w n.natAbs : ℂ) * e (lam * n) / (n : ℂ)

/-- The variation-norm prime Carleson operator `𝒱^r_ℙ f(x)` of (e:Carweight), with
`w(n) = Λ(|n|)` (e:wweight). -/
def primeVariation (r : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) : ℝ≥0∞ :=
  rVariation r (fun lam => modulatedSum (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f lam x)

/-- The maximally modulated operator `sup_{λ ∈ 𝕋} |∑_{n ≠ 0} f(x - n) w(|n|) e(λ n) / n|`:
`𝒞_ℙ` of (e:CP) for `w = Λ`, and `𝒞_v` of the Appendix A.1 lemma for `w = v`. -/
def carlesonMax (w : ℕ → ℝ) (f : ℤ →₀ ℂ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ lam ∈ Set.Ico (0 : ℝ) 1, ‖modulatedSum w f lam x‖ₑ

/-! ## The two compared statements

They are stated in the namespace `PrimeCarleson.Palomar`, so that `Solution.lean` can state
them again under these names and prove them from the development's theorems
`PrimeCarleson.variation_norm_prime_carleson` and `PrimeCarleson.prime_carleson_maximal`. -/

namespace Palomar

/-- **Theorem 1.3 (`t:main`).** For each `r > 2` there are `𝐜(r) , 𝐂(r)` with
`r' < 𝐜(r) < 2 < 𝐂(r)`, `𝐜(r) → 1` and `𝐂(r) → ∞` as `r → ∞`, and for each
`𝐜(r) < p < 𝐂(r)` a constant `0 < C_{p,r} < ∞` with `‖𝒱^r_ℙ f‖_{ℓ^p} ≤ C_{p,r} ‖f‖_{ℓ^p}`. -/
theorem variation_norm_prime_carleson :
    ∃ c C : ℝ → ℝ,
      (∀ r : ℝ, 2 < r → r / (r - 1) < c r ∧ c r < 2 ∧ 2 < C r) ∧
      Tendsto c atTop (𝓝 1) ∧ Tendsto C atTop atTop ∧
      ∀ r : ℝ, 2 < r → ∀ p : ℝ, c r < p → p < C r →
        ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
          eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
            ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  sorry

/-- **`t:carmax`.** For every `1 < p < ∞` there is `0 < C_p < ∞` with
`‖𝒞_ℙ f‖_{ℓ^p} ≤ C_p ‖f‖_{ℓ^p}`. -/
theorem prime_carleson_maximal :
    ∀ p : ℝ, 1 < p → ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f) (ENNReal.ofReal p)
          Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  sorry

end Palomar

end PrimeCarleson
