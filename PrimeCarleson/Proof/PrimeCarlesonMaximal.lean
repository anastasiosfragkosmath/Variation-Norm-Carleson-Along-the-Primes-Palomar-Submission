module

public import PrimeCarleson.Frozen.CarlesonMax
public import PrimeCarleson.Frozen.VariationNormCarlesonReal
public import PrimeCarleson.Frozen.VonMangoldtSubHeathBrownU3
public import PrimeCarleson.Proof.Paper.P6c.Root

/-!
# Provider for `PrimeCarleson.prime_carleson_maximal`

Proves the statement under the separate name
`PrimeCarleson.Proof.prime_carleson_maximal`.
Only `PrimeCarleson.Frozen.PrimeCarlesonMaximal` imports this module.

The proof in the main paper (formalized in `PrimeCarleson/Proof/Paper/`) derives the statement from
the [O+] Theorem 1.2 and [F+] Proposition 3.1 (`prime_carleson_maximal_of_inputs`); both are
statements proved elsewhere in this repository.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PrimeCarleson.Proof

/-- Theorem `t:carmax` of `sources/Variational_Carleson.tex`: the prime Carleson maximal operator
is bounded on `ℓ^p(ℤ)` for every `1 < p < ∞`. -/
theorem prime_carleson_maximal :
    ∀ p : ℝ, 1 < p → ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f) (ENNReal.ofReal p)
          Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
  Paper.prime_carleson_maximal_of_inputs PrimeCarleson.variation_norm_carleson_real
    PrimeCarleson.vonMangoldt_sub_heathBrown_U3

end PrimeCarleson.Proof
