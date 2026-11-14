module

public import PrimeCarleson.Proof.FplusProp21.Main
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# [F+] Proposition 2.1 applied to the paper's blocks `w_Q`

Source: main paper `e:highQ-var-L2-red`, L1411–L1415, where the paper applies [F+] Proposition 2.1
(also at L1509 and at L1265–L1268, `e:minor-U3-var-red`): for every `ε > 0` there is `C_ε` with
`‖w_Q‖_{U³([2^k])} ≤ C_ε Q^{-3/8+ε}` for all `k` and all `Q ≤ M(k) = exp(k^{1/10})`, where
`w_Q = ∑_{Q/2 < q ≤ Q} μ(q)/φ(q) c_q` (`blockWeight (Finset.Ioc (Q / 2) Q)`, the paper's `wQ Q`, so
`wQ (2^j)` for dyadic `Q`).

The paper applies [F+] Proposition 2.1 without writing out the following steps:

1. hypothesis (`pow_twenty_le_two_pow`): `8 ≤ Q ≤ exp(k^{1/10})` gives `Q^{20} ≤ 2^k`, since
   `t = k^{1/10} ≥ log 8 > 2` and `20 t ≤ t^{10} log 2 = k log 2`;
2. summation range: `(Q/2, Q] ∩ ℕ ⊆ [Q/2, Q]`, so `exists_gowersNormInterval_blockWeight_le`
   applies to `w_Q` directly (for every `Q`, not only dyadic `Q ≥ 8`, where the two blocks
   `(Q/2, Q]` and `[Q/2, Q)` coincide since `μ(Q/2) = μ(Q) = 0`);
3. small `Q < 8` (`gowersNormInterval_blockWeight_le_card`): `|w_Q(n)| ≤ |B| ≤ Q` (as
   `|c_q(n)| ≤ φ(q)`) and `‖g‖_{U³([N])} ≤ 2 sup_{[N]} |g|` (`Common.gowersNormInterval_three_le`);
4. norms: the `gowersNormInterval 3 N` is the paper's `U³([N])` on `[N] = {1, …, N}`;
5. `o(1)`: the statement has an explicit `C_ε` for every `ε > 0`, uniform in `k` and `Q`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.FplusProp21

/-- `|c_q(n)| ≤ φ(q)`. -/
theorem norm_ramanujanSum_le_totient (q : ℕ) (n : ℤ) : ‖ramanujanSum q n‖ ≤ q.totient := by
  unfold ramanujanSum
  refine (norm_sum_le _ _).trans ?_
  simp only [Goal0.norm_e, sum_const, nsmul_eq_mul, mul_one]
  rw [card_filter_coprime_Icc]

/-- `|w_B(n)| ≤ |B|`. -/
theorem norm_blockWeight_le_card (B : Finset ℕ) (n : ℤ) : ‖blockWeight B n‖ ≤ B.card := by
  unfold blockWeight
  refine (norm_sum_le _ _).trans ?_
  calc ∑ q ∈ B, ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) / (q.totient : ℝ) : ℂ) *
        ramanujanSum q n‖ ≤ ∑ _q ∈ B, (1 : ℝ) := by
        refine sum_le_sum fun q _ => ?_
        have hc : ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) / (q.totient : ℝ) : ℂ)‖ =
            |((ArithmeticFunction.moebius q : ℤ) : ℝ)| / (q.totient : ℝ) := by
          rw [norm_div]
          simp
        rw [norm_mul, hc]
        have hμ : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        rcases Nat.eq_zero_or_pos q.totient with h0 | hpos
        · simp [h0]
        · have hφ : (0 : ℝ) < q.totient := by exact_mod_cast hpos
          calc |((ArithmeticFunction.moebius q : ℤ) : ℝ)| / (q.totient : ℝ) * ‖ramanujanSum q n‖
              ≤ 1 / (q.totient : ℝ) * (q.totient : ℝ) :=
                mul_le_mul (div_le_div_of_nonneg_right hμ hφ.le)
                  (norm_ramanujanSum_le_totient q n) (norm_nonneg _) (by positivity)
            _ = 1 := by field_simp
    _ = B.card := by simp

/-- **The trivial bound** for small blocks: `‖w_B‖_{U³([N])} ≤ 2 |B|`. -/
theorem gowersNormInterval_blockWeight_le_card (B : Finset ℕ) (N : ℕ+) :
    gowersNormInterval 3 N (blockWeight B) ≤ 2 * B.card := by
  refine (Common.gowersNormInterval_three_le N _).trans ?_
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hsum : (N : ℝ)⁻¹ * ∑ n ∈ Icc (1 : ℤ) N, ‖blockWeight B n‖ ^ 2 ≤ (B.card : ℝ) ^ 2 := by
    calc (N : ℝ)⁻¹ * ∑ n ∈ Icc (1 : ℤ) N, ‖blockWeight B n‖ ^ 2
        ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Icc (1 : ℤ) N, (B.card : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun n _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_blockWeight_le_card B n) 2) (by positivity)
      _ = (B.card : ℝ) ^ 2 := by
          rw [sum_const, Int.card_Icc, nsmul_eq_mul]
          have : ((N : ℤ) + 1 - 1).toNat = (N : ℕ) := by omega
          rw [this]
          field_simp
  have hroot : ((B.card : ℝ) ^ 2) ^ ((1 : ℝ) / 2) = B.card := by
    have := Real.pow_rpow_inv_natCast (Nat.cast_nonneg B.card : (0 : ℝ) ≤ B.card) (n := 2)
      (by norm_num)
    rwa [show ((2 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 2 by norm_num] at this
  calc 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Icc (1 : ℤ) N, ‖blockWeight B n‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ 2 * ((B.card : ℝ) ^ 2) ^ ((1 : ℝ) / 2) := by
        gcongr
    _ = 2 * B.card := by rw [hroot]

/-- **The hypothesis `M ≥ Q^{20}` of Proposition 2.1** (step 1 above): if
`8 ≤ Q ≤ M(k) = exp(k^{1/10})`, then `Q^{20} ≤ 2^k`. -/
theorem pow_twenty_le_two_pow {Q : ℝ} (hQ : 8 ≤ Q) {k : ℕ}
    (hk : Q ≤ Real.exp ((k : ℝ) ^ ((1 : ℝ) / 10))) : Q ^ 20 ≤ (2 : ℝ) ^ k := by
  set t := (k : ℝ) ^ ((1 : ℝ) / 10) with ht
  have hQpos : 0 < Q := by linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogQ : Real.log Q ≤ t := (Real.log_le_iff_le_exp hQpos).2 hk
  have hlog8 : 2 < Real.log Q := by
    have h8 : Real.log 8 ≤ Real.log Q := Real.log_le_log (by norm_num) hQ
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have ht2 : 2 < t := by linarith
  have htk : t ^ 10 = k := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have h9 : (2 : ℝ) ^ 9 ≤ t ^ 9 := pow_le_pow_left₀ (by norm_num) ht2.le 9
  have hkey : 20 * Real.log Q ≤ k * Real.log 2 := by
    rw [← htk]
    calc 20 * Real.log Q ≤ 20 * t := by linarith
      _ ≤ t ^ 9 * 0.69 * t := by nlinarith
      _ ≤ t ^ 10 * Real.log 2 := by
          have : t ^ 10 = t ^ 9 * t := by ring
          rw [this]
          have ht0 : 0 ≤ t ^ 9 * t := by positivity
          nlinarith
  have hpos1 : 0 < Q ^ 20 := by positivity
  have hpos2 : (0 : ℝ) < 2 ^ k := by positivity
  rw [← Real.log_le_log_iff hpos1 hpos2, Real.log_pow, Real.log_pow]
  push_cast
  exact hkey

/-- **[F+] Proposition 2.1 applied to the paper's blocks** (Source: main paper `e:highQ-var-L2-red`,
L1411–L1415, general `Q`): for every `ε > 0` there is `C_ε` such that for all `k`, `N = 2^k` and all
integers `1 ≤ Q ≤ M(k) = exp(k^{1/10})`, `‖w_Q‖_{U³([2^k])} ≤ C_ε Q^{ε - 3/8}`, where
`w_Q = ∑_{Q/2 < q ≤ Q} μ(q)/φ(q) c_q = blockWeight (Ioc (Q/2) Q)`. -/
theorem exists_gowersNormInterval_blockWeight_Ioc_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (k : ℕ) (N : ℕ+), (N : ℕ) = 2 ^ k → ∀ Q : ℕ, 1 ≤ Q →
      (Q : ℝ) ≤ Real.exp ((k : ℝ) ^ ((1 : ℝ) / 10)) →
        gowersNormInterval 3 N (blockWeight (Ioc (Q / 2) Q)) ≤ C * (Q : ℝ) ^ (ε - 3 / 8) := by
  obtain ⟨C₀, hC₀⟩ := exists_gowersNormInterval_blockWeight_le hε
  refine ⟨max C₀ 98, fun k N hN Q hQ hQk => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hrpow0 : 0 ≤ (Q : ℝ) ^ (ε - 3 / 8) := Real.rpow_nonneg hQpos.le _
  have hB : ∀ q ∈ Ioc (Q / 2) Q, (Q : ℝ) / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q := by
    intro q hq
    rw [mem_Ioc] at hq
    have h1 : Q < q * 2 := (Nat.div_lt_iff_lt_mul (by norm_num)).1 hq.1
    have h1' : (Q : ℝ) < q * 2 := by exact_mod_cast h1
    exact ⟨by linarith, by exact_mod_cast hq.2⟩
  rcases Nat.lt_or_ge Q 8 with hQ8 | hQ8
  · -- small blocks: the trivial bound
    refine (gowersNormInterval_blockWeight_le_card _ N).trans ?_
    have hcard : ((Ioc (Q / 2) Q).card : ℝ) ≤ 7 := by
      rw [Nat.card_Ioc]
      have : Q - Q / 2 ≤ 7 := by omega
      exact_mod_cast this
    have hQ7 : (Q : ℝ) ≤ 7 := by exact_mod_cast (by omega : Q ≤ 7)
    have hlow : (1 : ℝ) / 7 ≤ (Q : ℝ) ^ (ε - 3 / 8) := by
      calc (1 : ℝ) / 7 ≤ (Q : ℝ)⁻¹ := by
            rw [one_div]
            exact inv_anti₀ hQpos hQ7
        _ = (Q : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
        _ ≤ (Q : ℝ) ^ (ε - 3 / 8) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    calc 2 * ((Ioc (Q / 2) Q).card : ℝ) ≤ 98 * (1 / 7) := by linarith
      _ ≤ max C₀ 98 * (Q : ℝ) ^ (ε - 3 / 8) :=
          mul_le_mul (le_max_right _ _) hlow (by norm_num) (by positivity)
  · -- `Q ≥ 8`: Proposition 2.1 with `M = 2^k ≥ Q^{20}`
    have hM : (Q : ℝ) ^ 20 ≤ (N : ℝ) := by
      have := pow_twenty_le_two_pow (by exact_mod_cast hQ8) hQk
      rw [show ((N : ℕ) : ℝ) = (2 : ℝ) ^ k by rw [hN]; push_cast; rfl]
      exact this
    refine (hC₀ Q hQ1 _ hB N hM).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hrpow0

/-- **[F+] Proposition 2.1 applied to the dyadic blocks** (Source: main paper `e:highQ-var-L2-red`,
L1411–L1415): for every `ε > 0` there is `C_ε` such that for all `k`, `N = 2^k` and all dyadic
`Q = 2^j ≤ M(k) = exp(k^{1/10})`, `‖w_{2^j}‖_{U³([2^k])} ≤ C_ε (2^j)^{-3/8 + ε}`,
`w_{2^j} = blockWeight (Ioc (2^j/2) 2^j)` (the block of the `heathBrownModel`). -/
theorem exists_gowersNormInterval_blockWeight_Ioc_two_pow_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (k : ℕ) (N : ℕ+), (N : ℕ) = 2 ^ k → ∀ j : ℕ,
      (2 : ℝ) ^ j ≤ Real.exp ((k : ℝ) ^ ((1 : ℝ) / 10)) →
        gowersNormInterval 3 N (blockWeight (Ioc (2 ^ j / 2) (2 ^ j))) ≤
          C * ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + ε) := by
  obtain ⟨C, hC⟩ := exists_gowersNormInterval_blockWeight_Ioc_le hε
  refine ⟨C, fun k N hN j hj => ?_⟩
  have h := hC k N hN (2 ^ j) (Nat.one_le_two_pow) (by exact_mod_cast hj)
  rw [show -(3 : ℝ) / 8 + ε = ε - 3 / 8 by ring]
  exact_mod_cast h

end PrimeCarleson.Proof.FplusProp21
