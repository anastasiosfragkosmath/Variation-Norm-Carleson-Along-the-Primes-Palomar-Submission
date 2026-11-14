module

public import PrimeCarleson.Proof.Paper.P3.TwoSided

/-!
# Lemma `e:U3maxmod`: the maximal `U³` estimate for modulated averages

Source: main paper `e:U3maxmod`, L718–L893 (statement L718–L731). Consumers: the variational
estimates of `P4b/` and the estimates of `P6c/`. The three estimates of the lemma, for `N ≥ 1`,
`w : [N] → ℂ`, `f` carried by `[-N, 2N]` (a reading of the lemma), and, for the third, `φ ∈ C²`,
`supp φ ⊆ [0, 1]`, `‖φ‖_{C²} ≤ 1`:

* `‖sup_λ |E_{n ∈ [N]} f(x-n) w(n) e(λ n)|‖_{L⁴([-N,2N])} ≲ ‖w‖_{U³([N])} ‖f‖_{U³([-N,2N])}`
  (`U3maxmod_L4`);
* `‖sup_λ |E_{n ∈ [N]} f(x-n) w(n) e(λ n)|‖_{L²([-N,2N])} ≲ ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`
  (`U3maxmod_L2`);
* `‖sup_λ |∑_n φ_N(n) f(x-n) w(n) e(λ n)|‖_{L²([-N,2N])} ≲ ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`
  (`smooth_L2_bound`),

all with the absolute constant `160` (`U3maxmod`). The forms used later (`ℓ²(ℤ)`, scale `2^k`,
`ψ_k`) are in `Localization.lean` (`U3maxmod_smooth_ell2Z`) and `TwoSided.lean`
(`U3maxmod_twoSided`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **`e:U3maxmod`** (Source: main paper `e:U3maxmod`, L718–L731): there is an absolute constant `C`
such that for all `N ≥ 1`, `w : ℤ → ℂ` (only the values on `[N]` enter) and `f` carried by
`[-N, 2N]`, with `A_λ f(x) = E_{n ∈ [N]} f(x-n) w(n) e(λ n)`:

1. `‖sup_λ |A_λ f|‖_{L⁴([-N,2N])} ≤ C ‖w‖_{U³([N])} ‖f‖_{U³([-N,2N])}`;
2. `‖sup_λ |A_λ f|‖_{L²([-N,2N])} ≤ C ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`;
3. for `φ ∈ C²` with `supp φ ⊆ [0, 1]` and `|φ|, |φ''| ≤ 1` (implied by `‖φ‖_{C²} ≤ 1`),
   `‖sup_λ |∑_n φ_N(n) f(x-n) w(n) e(λ n)|‖_{L²([-N,2N])} ≤
   C ‖w‖_{U³([N])} ‖f‖_{L²([-N,2N])}`. -/
theorem U3maxmod :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (w f : ℤ → ℂ), (∀ y, y ∉ maxWindow N → f y = 0) →
      lpNormOn 4 (maxWindow N)
          (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) ≤
        C * gowersNormOn 3 (bracket N) w * gowersNormOn 3 (maxWindow N) f ∧
      lpNormOn 2 (maxWindow N)
          (fun x => ((⨆ lam : ℝ, ‖modAverage N w f lam x‖ : ℝ) : ℂ)) ≤
        C * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f ∧
      ∀ φ : ℝ → ℂ, ContDiff ℝ 2 φ → Function.support φ ⊆ Set.Icc 0 1 → (∀ t, ‖φ t‖ ≤ 1) →
        (∀ t, ‖deriv (deriv φ) t‖ ≤ 1) →
        lpNormOn 2 (maxWindow N) (fun x => ((⨆ lam : ℝ, ‖weightedModSum
            (fun n : ℤ => dilate ((N : ℕ) : ℝ) φ (n : ℝ) * w n) f lam x‖ : ℝ) : ℂ)) ≤
          C * gowersNormOn 3 (bracket N) w * lpNormOn 2 (maxWindow N) f := by
  refine ⟨160, by norm_num, fun N w f hf => ⟨?_, ?_, fun φ hφ hs h0 h2 => ?_⟩⟩
  · have h := U3maxmod_L4 N w f hf
    have hn1 : 0 ≤ gowersNormOn 3 (bracket N) w := gowersNormOn_nonneg _ _ _
    have hn2 : 0 ≤ gowersNormOn 3 (maxWindow N) f := gowersNormOn_nonneg _ _ _
    nlinarith [mul_nonneg hn1 hn2]
  · have h := U3maxmod_L2 N w f hf
    have hn1 : 0 ≤ gowersNormOn 3 (bracket N) w := gowersNormOn_nonneg _ _ _
    have hn2 : 0 ≤ lpNormOn 2 (maxWindow N) f := lpNormOn_nonneg _ _ _
    nlinarith [mul_nonneg hn1 hn2]
  · have h := smooth_L2_bound N hφ hs h0 h2 w f hf
    linarith

end PrimeCarleson.Proof.Paper
