module

public import PrimeCarleson.Proof.Paper.Main.Range

/-!
# The conditional provider for `t:main`

Source: main paper `t:main`, L296–L335 (statement) and L1530–L1543, L1735–L1761 (proof). The paper
does not construct the range of `p` or prove the limits of `𝐜(r)`, `𝐂(r)` (L302–L305, L304); they
are supplied here.

* `bound_lt_two`, `bound_gt_two` (the range of `p`, L302–L305): every `p` strictly between `𝐜(r)`
  and `2`, respectively `2` and `𝐂(r)`, is of the form `1/p = θ'/2 + (1-θ')/s` with `s = 1 + 2/r`,
  respectively `s = r`, and `θ' > θ(r)`, hence `(1-θ')/θ'² < μ(r)` and `tmain_pair`
  (the bound for a fixed exponent, L1735–L1761) applies;
* `variation_norm_prime_carleson_of_inputs`: the statement of the theorem
  `PrimeCarleson.variation_norm_prime_carleson` (`t:main`), conditional on
  `hO : OplusVariationBound` (the `[O+]` statement) and `hF : FplusProp31` (the
  `[F+, Proposition 3.1]` statement). Both are proved in this repository, and the theorem's
  proof applies this theorem to them (`PrimeCarleson/Proof/VariationNormPrimeCarleson.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The range of `p` for `t:main`, lower half** (Source: main paper `t:main`, L1760–L1761): for
`r > 2` and
`𝐜(r) < p < 2` the `ℓ^p` bound for `V^r_P` holds. Here `1/p` lies between `1/2` and
`1/𝐜(r) = θ(r)/2 + (1-θ(r))/s` with `s = 1 + 2/r ∈ (r', 2)`, so `1/p = θ'/2 + (1-θ')/s` with
`θ' ∈ (θ(r), 1)`. -/
theorem bound_lt_two (hO : OplusVariationBound) (hF : FplusProp31) {r p : ℝ} (hr : 2 < r)
    (hcp : cR r < p) (hp2 : p < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hθ0 := thetaR_pos hr
  have hθ1 := thetaR_lt_one hr
  obtain ⟨hin1, hin2⟩ := cR_inner_bounds hr
  have hp0 : 0 < p := (lt_trans (div_pos hr0 hr1) (cR_gt hr)).trans hcp
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (r + 2) / r := ⟨_, rfl⟩
  have hsr : r / (r - 1) < s := by
    rw [hs, div_lt_div_iff₀ hr1 hr0]; nlinarith
  have hs2 : s < 2 := by rw [hs, div_lt_iff₀ hr0]; linarith
  have h1s : 1 / s = r / (r + 2) := by rw [hs, one_div_div]
  have hinpos : 0 < thetaR r / 2 + (1 - thetaR r) * (r / (r + 2)) := by linarith
  have hup : 1 / p < thetaR r / 2 + (1 - thetaR r) * (r / (r + 2)) := by
    have h : (thetaR r / 2 + (1 - thetaR r) * (r / (r + 2)))⁻¹ < p := hcp
    rw [inv_lt_comm₀ hinpos hp0] at h
    simpa [one_div] using h
  obtain ⟨θ', hθθ', hθ'1, hpθ⟩ := exists_theta_gt (u₀ := 1 / 2) (u₁ := 1 / s) (u := 1 / p)
    (c := thetaR r / 2 + (1 - thetaR r) * (r / (r + 2))) (θ := thetaR r) hθ1
    (by rw [h1s]; ring) (Or.inr ⟨one_div_lt_one_div_of_lt hp0 hp2, hup⟩)
  have hpθ' : 1 / p = θ' / 2 + (1 - θ') / s := by rw [hpθ]; ring
  exact tmain_pair hO hF hr hsr hs2.ne (hθ0.trans hθθ') hθ'1 hpθ'
    ((sub_div_sq_anti hθ0 hθθ'.le hθ'1.le).trans_lt (thetaR_cond hr))

/-- **The range of `p` for `t:main`, upper half** (Source: main paper `t:main`, L1760–L1761): for
`r > 2` and
`2 < p < 𝐂(r)` the `ℓ^p` bound for `V^r_P` holds. Here `1/p` lies between `1/𝐂(r) =
θ(r)/2 + (1-θ(r))/r` and `1/2`, so `1/p = θ'/2 + (1-θ')/r` with `θ' ∈ (θ(r), 1)`. -/
theorem bound_gt_two (hO : OplusVariationBound) (hF : FplusProp31) {r p : ℝ} (hr : 2 < r)
    (hp2 : 2 < p) (hpC : p < CR r) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hθ0 := thetaR_pos hr
  have hθ1 := thetaR_lt_one hr
  have hp0 : 0 < p := by linarith
  have hinpos : 0 < thetaR r / 2 + (1 - thetaR r) / r := by
    have : 0 < (1 - thetaR r) / r := div_pos (by linarith) hr0
    linarith
  have hup : thetaR r / 2 + (1 - thetaR r) / r < 1 / p := by
    have h : p < (thetaR r / 2 + (1 - thetaR r) / r)⁻¹ := hpC
    rw [lt_inv_comm₀ hp0 hinpos] at h
    simpa [one_div] using h
  obtain ⟨θ', hθθ', hθ'1, hpθ⟩ := exists_theta_gt (u₀ := 1 / 2) (u₁ := 1 / r) (u := 1 / p)
    (c := thetaR r / 2 + (1 - thetaR r) / r) (θ := thetaR r) hθ1
    (by ring) (Or.inl ⟨hup, one_div_lt_one_div_of_lt (by norm_num) hp2⟩)
  have hpθ' : 1 / p = θ' / 2 + (1 - θ') / r := by rw [hpθ]; ring
  have hsr : r / (r - 1) < r := by rw [div_lt_iff₀ hr1]; nlinarith
  exact tmain_pair hO hF hr hsr (by linarith) (hθ0.trans hθθ') hθ'1 hpθ'
    ((sub_div_sq_anti hθ0 hθθ'.le hθ'1.le).trans_lt (thetaR_cond hr))

/-- **`t:main` (Theorem 1.3), conditional on the `[O+]` and `[F+]` statements**
(Source: main paper `t:main`, L296–L309; proof L1735–L1761, where the paper omits the range of `p`
and the two limits; they are supplied by `cR`, `CR`, `bound_lt_two`,
`bound_gt_two`, `tendsto_cR` and `tendsto_CR`). Its conclusion is exactly the statement of the
theorem `PrimeCarleson.variation_norm_prime_carleson`: there are `c, C : ℝ → ℝ` chosen
before `r` with `r' < c(r) < 2 < C(r)` for all `r > 2`, `c(r) → 1`, `C(r) → ∞`, and for all `r > 2`
and all `c(r) < p < C(r)` a constant `0 < K` with `‖V^r_P f‖_{ℓ^p} ≤ K ‖f‖_{ℓ^p}` for every
finitely supported `f`. The only hypotheses are `hO : OplusVariationBound` (`[O+]`, the
`variation_norm_carleson_real`) and `hF : FplusProp31` (`[F+, Proposition 3.1]`, the
`vonMangoldt_sub_heathBrown_U3`). -/
theorem variation_norm_prime_carleson_of_inputs (hO : OplusVariationBound) (hF : FplusProp31) :
    ∃ c C : ℝ → ℝ,
      (∀ r : ℝ, 2 < r → r / (r - 1) < c r ∧ c r < 2 ∧ 2 < C r) ∧
      Tendsto c atTop (𝓝 1) ∧ Tendsto C atTop atTop ∧
      ∀ r : ℝ, 2 < r → ∀ p : ℝ, c r < p → p < C r →
        ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
          eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
            ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  refine ⟨cR, CR, fun r hr => ⟨cR_gt hr, cR_lt hr, two_lt_CR hr⟩, tendsto_cR, tendsto_CR, ?_⟩
  intro r hr p hcp hpC
  rcases lt_trichotomy p 2 with hlt | rfl | hgt
  · exact bound_lt_two hO hF hr hcp hlt
  · exact tmain_two hO hF hr
  · exact bound_gt_two hO hF hr hgt hpC

end PrimeCarleson.Proof.Paper
