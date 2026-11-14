module

public import PrimeCarleson.Proof.Paper.P4a.DyadicLimit

/-!
# The crude `V²` bound for modulated averages

Source: main paper `l:crudeV2lambda`, L926–L942, with its proof (L926–L1055); consumer:
`c:U3modvariation` (the interpolation in `r`, in `P4b/`).

For `N ≥ 1`, `w : [N] → ℂ` and a finitely supported `f : ℤ → ℂ`,
`‖V²(A_λ f : λ ∈ 𝕋)‖_{ℓ²(ℤ)} ≲ log(2N) ‖w‖_{L²([N])} ‖f‖_{ℓ²(ℤ)}`,
`A_λ f(x) = E_{n ∈ [N]} f(x-n) w(n) e(λn)` (`Paper.modAverage`), with the absolute constant `32π`
(`eLpNorm_variation_le_log`). The proof assembles the Rademacher–Menshov bound on dyadic grids
(L1024–L1042), the sum over scales (L1043–L1052) and the limiting argument (L1053–L1054) (file
`DyadicLimit`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **`l:crudeV2lambda`** with the explicit constant `32π`: for every `N ≥ 1`, `w : [N] → ℂ`
and finitely supported `f`,
`‖V²(A_λ f : λ ∈ 𝕋)‖_{ℓ²(ℤ)} ≤ 32π log(2N) ‖w‖_{L²([N])} ‖f‖_{ℓ²(ℤ)}`. -/
theorem eLpNorm_variation_le_log (N : ℕ+) (w f : ℤ → ℂ) (hf : (Function.support f).Finite) :
    eLpNorm (pointwiseVariation 2 (fun lam x => modAverage N w f lam x)) 2 Measure.count ≤
      ENNReal.ofReal
          (32 * Real.pi * Real.log (2 * ((N : ℕ) : ℝ)) * lpNormOn 2 (bracket N) w) *
        eLpNorm f 2 Measure.count :=
  eLpNorm_variation_Ico_le N w f (eLpNorm_variation_dyadicGrid_le_log N w f hf)

end PrimeCarleson.Proof.Paper
