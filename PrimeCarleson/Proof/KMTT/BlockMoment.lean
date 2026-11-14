module

public import PrimeCarleson.Proof.KMTT.Moment

/-!
# Moments of the Heath-Brown blocks `w_Q` from KMTT's moment bound

Source: main paper L1343–L1355 and `e:highQ-var-L2-red`, L1416–L1419, where the moments of `w_Q` are
taken from [FKT1, Lemma 3.1]. Here they are derived instead from KMTT Lemma 4.6, display (4.8)
(`PrimeCarleson.Proof.KMTT.moment_blockWeight_hbIndex`).

`w_Q = blockWeight (Finset.Ioc (Q / 2) Q)` for a natural number `Q` (natural-number division; for
`Q = 2^j` this is the block of `PrimeCarleson.heathBrownModel`).

* `blockWeight_Ioc_eq_sub`: `w_Q = Λ_{HB,Q+1} - Λ_{HB,⌊Q/2⌋+1}`;
* `moment_wQ`: for every `m ≥ 1` there is `C_m` with
  `E_{n ∈ [N]} |w_Q(n)|^m ≤ C_m (1 + log Q)^(2^m + m)` for every natural `Q ≥ 1` (dyadic or not)
  and every real `N ≥ 1`;
* `norm_L2_wQ_le`: `‖w_Q‖_{L²([N])} ≤ C (1 + log Q)^3` for every `N ≥ 1` (in particular
  `N = 2^k`), and `exists_pow_log_le_rpow`: `(1 + log Q)^3 ≤ C_ε Q^ε` for every `ε > 0`
  (`≲ Q^{o(1)}`).
-/

@[expose] public noncomputable section

open PrimeCarleson Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.KMTT

/-- `w_Q = Λ_{HB,Q+1} - Λ_{HB,⌊Q/2⌋+1}` for a natural number `Q`. -/
theorem blockWeight_Ioc_eq_sub (Q : ℕ) (n : ℤ) :
    blockWeight (Finset.Ioc (Q / 2) Q) n =
      blockWeight (hbIndex ((Q + 1 : ℕ) : ℝ)) n -
        blockWeight (hbIndex (((Q / 2 : ℕ) + 1 : ℕ) : ℝ)) n := by
  have h1 : hbIndex ((Q + 1 : ℕ) : ℝ) = Finset.Ico 1 (Q + 1) := by
    unfold hbIndex; rw [Nat.ceil_natCast]
  have h2 : hbIndex (((Q / 2 : ℕ) + 1 : ℕ) : ℝ) = Finset.Ico 1 (Q / 2 + 1) := by
    unfold hbIndex; rw [Nat.ceil_natCast]
  rw [h1, h2, eq_sub_iff_add_eq]
  have hsub : Finset.Ico 1 (Q / 2 + 1) ⊆ Finset.Ico 1 (Q + 1) := by
    intro q hq
    rw [Finset.mem_Ico] at hq ⊢
    omega
  have hset : Finset.Ioc (Q / 2) Q = Finset.Ico 1 (Q + 1) \ Finset.Ico 1 (Q / 2 + 1) := by
    ext q
    simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Ico]
    omega
  unfold blockWeight
  rw [hset]
  exact Finset.sum_sdiff hsub

/-- `⟨Log Q'⟩ ≤ 2 (1 + log Q)` for `1 ≤ Q' ≤ 2 Q`. -/
theorem logBracket_le_two_mul_one_add_log {Q Q' : ℝ} (hQ' : 1 ≤ Q') (hQ : 1 ≤ Q)
    (h : Q' ≤ 2 * Q) : logBracket Q' ≤ 2 * (1 + Real.log Q) := by
  have h1 := logBracket_le Q'
  have h2 : (logScale Q' : ℝ) ≤ Real.logb 2 Q' :=
    Nat.floor_le (Real.logb_nonneg (by norm_num) hQ')
  have h3 : Real.logb 2 Q' ≤ Real.logb 2 (2 * Q) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) h
  have h4 : Real.logb 2 (2 * Q) = 1 + Real.logb 2 Q := by
    rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)]
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have h5 : Real.logb 2 Q ≤ 2 * Real.log Q := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- The `L^m` moment of the difference of two blocks: `|a - b|^m ≤ 2^(m-1) (|a|^m + |b|^m)`. -/
theorem norm_sub_pow_le {a b : ℂ} (m : ℕ) :
    ‖a - b‖ ^ m ≤ 2 ^ (m - 1) * (‖a‖ ^ m + ‖b‖ ^ m) :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) m).trans
    (add_pow_le (norm_nonneg a) (norm_nonneg b) m)

/-- Moments of `w_Q = Λ_{HB,Q+1} - Λ_{HB,⌊Q/2⌋+1}` (Source: main paper `e:highQ-var-L2-red`,
L1416–L1419): for every `m ≥ 1` there is `C_m` such that
`E_{n ∈ [N]} |w_Q(n)|^m ≤ C_m (1 + log Q)^(2^m + m)` for every natural `Q ≥ 1` and every real
`N ≥ 1`. -/
theorem moment_wQ (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : ℕ) (N : ℝ), 1 ≤ Q → 1 ≤ N →
      (1 / ((intervalN N).card : ℝ)) *
          ∑ n ∈ intervalN N, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m ≤
        C * (1 + Real.log Q) ^ (2 ^ m + m) := by
  obtain ⟨C0, hC0, h0⟩ := moment_blockWeight_hbIndex m hm
  refine ⟨2 ^ (m - 1) * C0 * (2 * 2 ^ (2 ^ m + m)), by positivity, fun Q N hQ hN => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hcard : (0 : ℝ) < ((intervalN N).card : ℝ) := by
    rw [card_intervalN hN]; exact_mod_cast Nat.floor_pos.mpr hN
  have hA := h0 ((Q + 1 : ℕ) : ℝ) N (by push_cast; linarith) hN
  have hB := h0 (((Q / 2 : ℕ) + 1 : ℕ) : ℝ) N (by push_cast; linarith) hN
  have hLA := logBracket_le_two_mul_one_add_log (Q := Q) (Q' := ((Q + 1 : ℕ) : ℝ))
    (by push_cast; linarith) hQ1 (by push_cast; linarith)
  have hLB := logBracket_le_two_mul_one_add_log (Q := Q) (Q' := (((Q / 2 : ℕ) + 1 : ℕ) : ℝ))
    (by push_cast; linarith) hQ1 (by
      have : (Q / 2 : ℕ) ≤ Q := Nat.div_le_self _ _
      have : ((Q / 2 : ℕ) : ℝ) ≤ Q := by exact_mod_cast this
      push_cast; linarith)
  have hL1 : 0 ≤ logBracket ((Q + 1 : ℕ) : ℝ) := (logBracket_pos _).le
  have hL2 : 0 ≤ logBracket (((Q / 2 : ℕ) + 1 : ℕ) : ℝ) := (logBracket_pos _).le
  have hPA : logBracket ((Q + 1 : ℕ) : ℝ) ^ (2 ^ m + m) ≤ (2 * (1 + Real.log Q)) ^ (2 ^ m + m) :=
    pow_le_pow_left₀ hL1 hLA _
  have hPB : logBracket (((Q / 2 : ℕ) + 1 : ℕ) : ℝ) ^ (2 ^ m + m) ≤
      (2 * (1 + Real.log Q)) ^ (2 ^ m + m) := pow_le_pow_left₀ hL2 hLB _
  have hpt : ∀ n ∈ intervalN N, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m ≤
      2 ^ (m - 1) * (‖blockWeight (hbIndex ((Q + 1 : ℕ) : ℝ)) n‖ ^ m +
        ‖blockWeight (hbIndex (((Q / 2 : ℕ) + 1 : ℕ) : ℝ)) n‖ ^ m) := by
    intro n _
    rw [blockWeight_Ioc_eq_sub]
    exact norm_sub_pow_le m
  have hsum : ∑ n ∈ intervalN N, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m ≤
      2 ^ (m - 1) * (∑ n ∈ intervalN N, ‖blockWeight (hbIndex ((Q + 1 : ℕ) : ℝ)) n‖ ^ m +
        ∑ n ∈ intervalN N, ‖blockWeight (hbIndex (((Q / 2 : ℕ) + 1 : ℕ) : ℝ)) n‖ ^ m) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hc : (0 : ℝ) ≤ 1 / ((intervalN N).card : ℝ) := by positivity
  calc (1 / ((intervalN N).card : ℝ)) *
        ∑ n ∈ intervalN N, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m
      ≤ (1 / ((intervalN N).card : ℝ)) * (2 ^ (m - 1) *
        (∑ n ∈ intervalN N, ‖blockWeight (hbIndex ((Q + 1 : ℕ) : ℝ)) n‖ ^ m +
          ∑ n ∈ intervalN N, ‖blockWeight (hbIndex (((Q / 2 : ℕ) + 1 : ℕ) : ℝ)) n‖ ^ m)) :=
        mul_le_mul_of_nonneg_left hsum hc
    _ = 2 ^ (m - 1) * ((1 / ((intervalN N).card : ℝ)) *
          ∑ n ∈ intervalN N, ‖blockWeight (hbIndex ((Q + 1 : ℕ) : ℝ)) n‖ ^ m +
        (1 / ((intervalN N).card : ℝ)) *
          ∑ n ∈ intervalN N, ‖blockWeight (hbIndex (((Q / 2 : ℕ) + 1 : ℕ) : ℝ)) n‖ ^ m) := by
        ring
    _ ≤ 2 ^ (m - 1) * (C0 * (2 * (1 + Real.log Q)) ^ (2 ^ m + m) +
          C0 * (2 * (1 + Real.log Q)) ^ (2 ^ m + m)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (hA.trans ?_) (hB.trans ?_)) (by positivity)
        · exact mul_le_mul_of_nonneg_left hPA hC0
        · exact mul_le_mul_of_nonneg_left hPB hC0
    _ = 2 ^ (m - 1) * C0 * (2 * 2 ^ (2 ^ m + m)) * (1 + Real.log Q) ^ (2 ^ m + m) := by
        rw [mul_pow]; ring

/-- Part (a) of the moment bounds of `w_Q` (Source: main paper `e:highQ-var-L2-red`, L1416–L1419):
`‖w_Q‖_{L²([N])} ≤ C (1 + log Q)^3` for every real `N ≥ 1` (in particular `N = 2^k`) and every
natural `Q ≥ 1`; here `‖f‖_{L²([N])}² = E_{n ∈ [N]} |f(n)|²`. -/
theorem norm_L2_wQ_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : ℕ) (N : ℝ), 1 ≤ Q → 1 ≤ N →
      Real.sqrt ((1 / ((intervalN N).card : ℝ)) *
          ∑ n ∈ intervalN N, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ 2) ≤
        C * (1 + Real.log Q) ^ 3 := by
  obtain ⟨C2, hC2, h2⟩ := moment_wQ 2 (by norm_num)
  refine ⟨Real.sqrt C2, Real.sqrt_nonneg _, fun Q N hQ hN => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have := h2 Q N hQ hN
  calc _ ≤ C2 * (1 + Real.log Q) ^ (2 ^ 2 + 2) := this
    _ = (Real.sqrt C2 * (1 + Real.log Q) ^ 3) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC2, ← pow_mul]
        norm_num

/-- `(1 + log Q)^3 ≲ Q^{o(1)}`: for every `ε > 0`, `(1 + log Q)^3 ≤ C_ε Q^ε` for `Q ≥ 1`. -/
theorem exists_pow_log_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 ≤ Q → (1 + Real.log Q) ^ 3 ≤ C * Q ^ ε := by
  refine ⟨(1 + 3 / ε) ^ 3, by positivity, fun Q hQ => ?_⟩
  have hδ : 0 < ε / 3 := by positivity
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : Real.log Q ≤ Q ^ (ε / 3) / (ε / 3) := Real.log_le_rpow_div hQ0 hδ
  have h2 : 1 ≤ Q ^ (ε / 3) := Real.one_le_rpow hQ hδ.le
  have h3 : 1 + Real.log Q ≤ (1 + 3 / ε) * Q ^ (ε / 3) := by
    have : Q ^ (ε / 3) / (ε / 3) = 3 / ε * Q ^ (ε / 3) := by field_simp
    nlinarith
  have hQε : (Q ^ (ε / 3)) ^ 3 = Q ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0]
    congr 1
    push_cast; ring
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  calc (1 + Real.log Q) ^ 3 ≤ ((1 + 3 / ε) * Q ^ (ε / 3)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) h3 3
    _ = (1 + 3 / ε) ^ 3 * Q ^ ε := by rw [mul_pow, hQε]

/-- The power mean inequality for the uniform average on a nonempty finite set, `1 ≤ p ≤ 2`:
`(E |f|^p)^{1/p} ≤ (E |f|²)^{1/2}` (Hölder). -/
theorem avg_rpow_le_sqrt_avg_sq {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    ((1 / (S.card : ℝ)) * ∑ i ∈ S, f i ^ p) ^ (1 / p) ≤
      ((1 / (S.card : ℝ)) * ∑ i ∈ S, f i ^ 2) ^ (1 / (2 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hw : ∑ _i ∈ S, (1 / (S.card : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have h1 := Real.rpow_arith_mean_le_arith_mean_rpow S (fun _ => 1 / (S.card : ℝ))
    (fun i => f i ^ p) (fun _ _ => by positivity) hw
    (fun i _ => Real.rpow_nonneg (hf i) _) (p := 2 / p) (by rw [le_div_iff₀ hp0]; linarith)
  have h2 : ∀ i ∈ S, (1 / (S.card : ℝ)) * (f i ^ p) ^ (2 / p) =
      (1 / (S.card : ℝ)) * f i ^ 2 := by
    intro i _
    rw [← Real.rpow_mul (hf i), mul_div_cancel₀ _ hp0.ne', Real.rpow_two]
  rw [Finset.sum_congr rfl h2] at h1
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
  have hA : 0 ≤ (1 / (S.card : ℝ)) * ∑ i ∈ S, f i ^ p :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _)
  have h3 : (1 / (S.card : ℝ) * ∑ i ∈ S, f i ^ p) ^ (1 / p) =
      ((1 / (S.card : ℝ) * ∑ i ∈ S, f i ^ p) ^ (2 / p)) ^ (1 / (2 : ℝ)) := by
    rw [← Real.rpow_mul hA]
    congr 1
    field_simp
  rw [h3]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hA _) h1 (by norm_num)

/-- An even nonnegative function summed over integers `1 ≤ |n| ≤ N` is at most twice its sum over
`[N]`. -/
theorem sum_le_two_mul_of_even {S : Finset ℤ} {N : ℝ} (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hfe : ∀ n, f (-n) = f n) (hsub : ∀ n ∈ S, 1 ≤ |n| ∧ |(n : ℝ)| ≤ N) :
    ∑ n ∈ S, f n ≤ 2 * ∑ n ∈ intervalN N, f n := by
  have hpos : ∑ n ∈ S.filter (fun n => 0 < n), f n ≤ ∑ n ∈ intervalN N, f n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => hf0 n
    rw [Finset.mem_filter] at hn
    obtain ⟨h1, h2⟩ := hsub n hn.1
    rw [mem_intervalN]
    refine ⟨by omega, ?_⟩
    rwa [abs_of_pos (by exact_mod_cast hn.2)] at h2
  have hneg : ∑ n ∈ S.filter (fun n => ¬ 0 < n), f n ≤ ∑ n ∈ intervalN N, f n := by
    calc ∑ n ∈ S.filter (fun n => ¬ 0 < n), f n
        = ∑ n ∈ (S.filter (fun n => ¬ 0 < n)).image Neg.neg, f n := by
          rw [Finset.sum_image (fun a _ b _ h => neg_injective h)]
          simp only [hfe]
      _ ≤ ∑ n ∈ intervalN N, f n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => hf0 n
          rw [Finset.mem_image] at hn
          obtain ⟨m, hm, rfl⟩ := hn
          rw [Finset.mem_filter] at hm
          obtain ⟨h1, h2⟩ := hsub m hm.1
          have hm0 : m < 0 := by
            rcases lt_or_gt_of_ne (show m ≠ 0 by rintro rfl; simp at h1) with h | h
            · exact h
            · exact absurd h hm.2
          rw [mem_intervalN]
          rw [abs_of_neg (by exact_mod_cast hm0)] at h2
          refine ⟨by omega, ?_⟩
          push_cast; exact h2
  have hsplit : ∑ n ∈ S, f n = ∑ n ∈ S.filter (fun n => 0 < n), f n +
      ∑ n ∈ S.filter (fun n => ¬ 0 < n), f n := by
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  linarith

end PrimeCarleson.Proof.KMTT
