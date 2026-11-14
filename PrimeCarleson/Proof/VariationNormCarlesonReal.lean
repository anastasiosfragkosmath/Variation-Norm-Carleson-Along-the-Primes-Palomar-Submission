module

public import PrimeCarleson.Frozen.RVariationOn
public import PrimeCarleson.Frozen.PartialFourierIntegral
public import PrimeCarleson.Proof.Oplus.Theorem.Main

/-!
# Provider for `PrimeCarleson.variation_norm_carleson_real`

Proves the statement under the separate name
`PrimeCarleson.Proof.variation_norm_carleson_real`.
Only `PrimeCarleson.Frozen.VariationNormCarlesonReal` imports this module.

The proof is `PrimeCarleson.Proof.Oplus.variation_norm_carleson_real_proof`
(`PrimeCarleson/Proof/Oplus/Theorem/Main.lean`), the [O+] Theorem 1.2 assembled from the sections
of the proof formalized in `PrimeCarleson/Proof/Oplus/` and two external inputs: the
square-function estimate of Jones–Kaufman–Rosenblatt–Wierdl (`varestpsi` at `p = 2`) and the
tile-energy estimate and Fefferman–Stein interpolation, along the route adopted here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace PrimeCarleson.Proof

/-- [O+] Theorem 1.2: the partial Fourier integral is bounded from `L^p(ℝ)` into `L^p(V^r)` for
`r > 2` and `p > r'`, on Schwartz functions. -/
theorem variation_norm_carleson_real :
    ∀ r : ℝ, 2 < r → ∀ p : ℝ, r / (r - 1) < p → ∃ C : ℝ, ∀ f : 𝓢(ℝ, ℂ),
      eLpNorm (fun x => rVariationOn r Set.univ (fun ξ => partialFourierIntegral f ξ x))
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume :=
  Oplus.variation_norm_carleson_real_proof

end PrimeCarleson.Proof
