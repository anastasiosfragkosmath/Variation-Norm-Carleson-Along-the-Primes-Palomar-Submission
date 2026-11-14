module

public import PrimeCarleson.Frozen.PrimeVariation
public import PrimeCarleson.Frozen.VariationNormCarlesonReal
public import PrimeCarleson.Frozen.VonMangoldtSubHeathBrownU3
public import PrimeCarleson.Proof.Paper.Main.Root

/-!
# Provider for `PrimeCarleson.variation_norm_prime_carleson`

Proves the statement under the separate name
`PrimeCarleson.Proof.variation_norm_prime_carleson`.
Only `PrimeCarleson.Frozen.VariationNormPrimeCarleson` imports this module.

The proof in the main paper (formalized in `PrimeCarleson/Proof/Paper/`) derives the statement from
the [O+] Theorem 1.2 and [F+] Proposition 3.1 (`variation_norm_prime_carleson_of_inputs`);
both are statements proved elsewhere in this repository.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PrimeCarleson.Proof

/-- Theorem `t:main` of `sources/Variational_Carleson.tex`: the `r`-variation of the prime Carleson
sums is bounded on `ℓ^p(ℤ)` for `c(r) < p < C(r)`, with `c(r) → 1` and `C(r) → ∞`. -/
theorem variation_norm_prime_carleson :
    ∃ c C : ℝ → ℝ,
      (∀ r : ℝ, 2 < r → r / (r - 1) < c r ∧ c r < 2 ∧ 2 < C r) ∧
      Tendsto c atTop (𝓝 1) ∧ Tendsto C atTop atTop ∧
      ∀ r : ℝ, 2 < r → ∀ p : ℝ, c r < p → p < C r →
        ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
          eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
            ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count :=
  Paper.variation_norm_prime_carleson_of_inputs PrimeCarleson.variation_norm_carleson_real
    PrimeCarleson.vonMangoldt_sub_heathBrown_U3

end PrimeCarleson.Proof
