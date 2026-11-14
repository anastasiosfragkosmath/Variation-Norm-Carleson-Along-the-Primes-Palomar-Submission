module

public import PrimeCarleson.Proof.Paper.P8.EntropyLemma
public import PrimeCarleson.Proof.Paper.P9.VarCarInput
public import PrimeCarleson.Proof.Paper.P5.Support
public import PrimeCarleson.Proof.Paper.P7.Adapter

/-!
# The auxiliary exponents of `p:transferprop` and the variational input for `K_Q`

Source: main paper `p:transferprop`, L2238–L2246, in the form where the entropy argument is run at a
fixed exponent and the loss is a power of `Q`).

* `transfer_exponent_choice`: `r_♯ = 4` and `s_e = 40/(20 - ε)` satisfy `2 < s_e < 4`,
  `γ(4, s_e) = 2 (s_e - 2)/s_e = ε/10` and `E(4, s_e) ≤ 7.35 (6 + 29/ε)`;
* `KQ_hat_sup`: `sup |K̂_Q| ≤ C₀` and `V(K̂_Q) ≤ C₀` uniformly in `Q = 2^j`
  (the base point factor `M₀` of Theorem B; absolute, from `KQhat_bv`);
* `mt_variational_bound`: for `s > 2` and `l:varcarZ` (`LVarCarZ s Cv`), the variation estimate
  `‖V^s(m_t^v * F : t ∈ T)‖_{ℓ²} ≤ Cv C₀ ‖F‖` for finite `T ⊆ [0, 1)` (the paper's
  `t ∈ 𝕋`, as finite subsets of one period).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- **The auxiliary exponents of `p:transferprop`**: for `0 < ε ≤ 1/100`, `r_♯ = 4` and
`s_e = 40/(20 - ε) ∈ (2, 40/19]` satisfy `2 < s_e < 4`, `γ(4, s_e) = ε/10` and
`E(4, s_e) ≤ 7.35 (6 + 29/ε)`. -/
theorem transfer_exponent_choice {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) :
    2 < 40 / (20 - ε) ∧ 40 / (20 - ε) < 4 ∧ 40 / (20 - ε) ≤ 40 / 19 ∧
      entropyGamma 4 (40 / (20 - ε)) = ε / 10 ∧
      entropyConst 4 (40 / (20 - ε)) ≤ 7.35 * (6 + 29 / ε) := by
  have h20 : 0 < 20 - ε := by linarith
  have hs2 : 2 < 40 / (20 - ε) := by
    rw [lt_div_iff₀ h20]; linarith
  have hs4 : 40 / (20 - ε) < 4 := by
    rw [div_lt_iff₀ h20]; linarith
  refine ⟨hs2, hs4, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ h20 (by norm_num)]; linarith
  · unfold entropyGamma
    have hne : (20 - ε) ≠ 0 := h20.ne'
    field_simp
    ring
  · refine (entropyConst_le hs2 hs4).trans ?_
    have hsm : 40 / (20 - ε) - 2 = 2 * ε / (20 - ε) := by
      field_simp
      ring
    have h1 : 2.89 / (40 / (20 - ε) - 2) ≤ 29 / ε := by
      rw [hsm, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hε]
      nlinarith
    have h2 : 1.45 * 4 / (4 - 40 / (20 - ε)) ≤ 4 := by
      have : 4 - 40 / (20 - ε) = (40 - 4 * ε) / (20 - ε) := by
        field_simp
        ring
      rw [this, div_div_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith

/-- **The supremum bound for `K̂_Q`** (with `KQ_multiplier_properties` of `P5/Support.lean`): there
is an absolute `C₀ ≥ 0` with `sup_β |K̂_Q(β)| ≤ C₀` and `V(K̂_Q) ≤ C₀` for every `Q`, `D₀`, `ε`. -/
theorem KQ_hat_sup (S : KQSetup) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (j : ℕ), (∀ β : ℝ, ‖S.KQhat (2 ^ j) β‖ ≤ C₀) ∧
      eVariationOn (S.KQhat (2 ^ j)) Set.univ ≤ ENNReal.ofReal C₀ := by
  obtain ⟨C, hC0, hC⟩ := S.KQhat_bv
  exact ⟨C, hC0, fun j => hC S.P (2 ^ j)⟩

/-- **The variational bound for `m_t^v * F`** (Source: main paper `p:transferprop`, L2244–L2246, in
the form used here): under (C1) `SupportBlock` and `l:varcarZ` at the exponent `s`
(`LVarCarZ s Cv`),
for every finite `T ⊆ [0, 1)` in the chart `(θ, θ + 1)` (up to the support radius `δ/N(Q)` of
`K̂_Q`) and every density `H ∈ L²`, `‖V^s(m_t^v * F : t ∈ T)‖_{ℓ²} ≤ Cv C₀ ‖F‖_{ℓ²}`,
`F = invFZ θ H`. -/
theorem mt_variational_bound (S : KQSetup) (hS : S.P.SupportBlock S.δ) {s Cv : ℝ} (hs : 1 ≤ s)
    (hCv : 0 ≤ Cv) (hv : LVarCarZ s Cv) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (j : ℕ)
    (hKb : ∀ β : ℝ, ‖S.KQhat (2 ^ j) β‖ ≤ C₀)
    (hbv : eVariationOn (S.KQhat (2 ^ j)) Set.univ ≤ ENNReal.ofReal C₀)
    {θ : ℝ} {T : Set ℝ} (hT : T.Finite) (hT01 : T ⊆ Set.Ico 0 1)
    (hchart : ∀ t ∈ T, θ < t - S.δ / S.P.NQ (2 ^ j) ∧ t + S.δ / S.P.NQ (2 ^ j) < θ + 1)
    {H : ℝ → ℂ} (hH : ChartL2 θ H) :
    (∑' x : ℤ, rVariationOn s T
      (fun t => invFZ θ (fun β => S.KQmult (2 ^ j) t β * H β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Cv * C₀) * l2enorm (invFZ θ H) := by
  have hsup : Function.support (S.KQhat (2 ^ j)) ⊆ Set.Icc (-(1 / 20)) (1 / 20) := by
    refine (S.support_KQhat_subset_of_block hS j).trans ?_
    have h1 : (1 : ℝ) / (100 * (2 : ℝ) ^ j) ≤ 1 / 20 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      linarith
    intro β hβ
    rw [Set.mem_Icc] at hβ ⊢
    constructor <;> linarith [hβ.1, hβ.2]
  exact S.variation_hyp hv hs hC₀ hCv hbv hsup hKb hT hT01 hchart hH

end PrimeCarleson.Proof.Paper
