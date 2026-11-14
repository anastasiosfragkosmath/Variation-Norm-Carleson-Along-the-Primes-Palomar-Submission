module

public import PrimeCarleson.Proof.KMTT.DivisorMoment

/-!
# KMTT's moment bound for the Heath-Brown approximant (Lemma 4.6, display (4.8))

Source: [KMTT] `lambdaq-moment`, L853–L871 (arXiv:2409.10510v2,
[KMTT] TeX; proof L874–L923):
for every integer `m ≥ 1` there is `C_m` such that for all real `Q ≥ 1` and `N ≥ 1`,
`E_{n ∈ [N]} |Λ_{HB,Q}(n)|^m ≤ C_m ⟨Log Q⟩^(2^m + m)`, where `[N] = {n ∈ ℤ : 1 ≤ n ≤ N}`,
`Λ_{HB,Q} = blockWeight {q : 1 ≤ q < Q}` and `⟨Log Q⟩ = logBracket Q`.

The proof combines the pointwise bound `|Λ_{HB,Q}(n)| ≤ C τ(n, Q) ⟨Log Q⟩`
(`norm_blockWeight_hbIndex_le`, [KMTT] `lhb`, `lambdad`, `lambdaq-bound`, L853–L866) with the
moment of the truncated divisor function (`exists_sum_truncDivisor_pow_le`, [KMTT], L891–L892,
`Q ≥ 8`); the range `1 ≤ Q < 8` ([KMTT], L890) has `τ(n, Q) ≤ 7`. -/

@[expose] public noncomputable section

open PrimeCarleson Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.KMTT

/-- KMTT's `[N] = {n ∈ ℤ : 1 ≤ n ≤ N}` for real `N` (L295): the integers `1, …, ⌊N⌋`. -/
def intervalN (N : ℝ) : Finset ℤ := Finset.Icc 1 ⌊N⌋

/-- Membership in `[N]`: `1 ≤ n ≤ N`. -/
theorem mem_intervalN {N : ℝ} {n : ℤ} : n ∈ intervalN N ↔ 1 ≤ n ∧ (n : ℝ) ≤ N := by
  unfold intervalN
  rw [Finset.mem_Icc, Int.le_floor]

/-- Sums over `{1, …, M} ⊆ ℤ` are sums over `{1, …, M} ⊆ ℕ`. -/
theorem sum_Icc_int_one_eq (M : ℕ) (f : ℤ → ℝ) :
    ∑ n ∈ Finset.Icc (1 : ℤ) M, f n = ∑ m ∈ Finset.Icc 1 M, f (m : ℤ) := by
  refine Finset.sum_nbij' (fun n => n.toNat) (fun m => (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    omega
  · intro a ha
    simp
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    congr 1
    omega

/-- `[N] = {1, …, ⌊N⌋₊}` for `N ≥ 1`. -/
theorem intervalN_eq {N : ℝ} (hN : 1 ≤ N) : intervalN N = Finset.Icc (1 : ℤ) (⌊N⌋₊ : ℤ) := by
  unfold intervalN
  rw [Int.natCast_floor_eq_floor (by linarith)]

/-- `#[N] = ⌊N⌋₊` for `N ≥ 1`. -/
theorem card_intervalN {N : ℝ} (hN : 1 ≤ N) : ((intervalN N).card : ℝ) = ⌊N⌋₊ := by
  rw [intervalN_eq hN, Int.card_Icc]
  have : 1 ≤ ⌊N⌋₊ := Nat.le_floor (by exact_mod_cast hN)
  have h2 : ((⌊N⌋₊ : ℤ) + 1 - 1).toNat = ⌊N⌋₊ := by omega
  rw [h2]

/-- `τ(n, Q) ≤ 7` for `Q < 8` (the divisors `ℓ < Q`, `ℓ ≤ 7`). -/
theorem truncDivisor_le_seven {Q : ℝ} (hQ : Q < 8) (n : ℕ) : truncDivisor n Q ≤ 7 := by
  unfold truncDivisor
  calc (n.divisors.filter fun ℓ : ℕ => (ℓ : ℝ) < Q).card ≤ (Finset.Icc 1 7).card := by
        refine Finset.card_le_card fun ℓ hℓ => ?_
        rw [Finset.mem_filter] at hℓ
        have h1 : 1 ≤ ℓ := Nat.pos_of_mem_divisors hℓ.1
        have h2 : (ℓ : ℝ) < 8 := hℓ.2.trans hQ
        have h3 : ℓ < 8 := by exact_mod_cast h2
        exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
    _ = 7 := by simp

/-- KMTT Lemma 4.6, display (4.8): for every integer `m ≥ 1` there is `C_m` such that for all real
`Q ≥ 1` and `N ≥ 1`,
`E_{n ∈ [N]} |Λ_{HB,Q}(n)|^m ≤ C_m ⟨Log Q⟩^(2^m + m)`. -/
theorem moment_blockWeight_hbIndex (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q N : ℝ), 1 ≤ Q → 1 ≤ N →
      (1 / ((intervalN N).card : ℝ)) *
          ∑ n ∈ intervalN N, ‖blockWeight (hbIndex Q) n‖ ^ m ≤
        C * logBracket Q ^ (2 ^ m + m) := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_sum_truncDivisor_pow_le hm
  refine ⟨(32 * Real.exp 65) ^ m * (Cm + 7 ^ m), by positivity, fun Q N hQ hN => ?_⟩
  have hL1 := one_le_logBracket Q
  have hL0 := logBracket_pos Q
  have hM1 : 1 ≤ ⌊N⌋₊ := Nat.le_floor (by exact_mod_cast hN)
  have hM0 : (0 : ℝ) < ⌊N⌋₊ := by exact_mod_cast hM1
  rw [card_intervalN hN, intervalN_eq hN,
    sum_Icc_int_one_eq ⌊N⌋₊ (fun n => ‖blockWeight (hbIndex Q) n‖ ^ m)]
  set M := ⌊N⌋₊ with hM
  have hpt : ∑ n ∈ Finset.Icc 1 M, ‖blockWeight (hbIndex Q) (n : ℤ)‖ ^ m ≤
      (32 * Real.exp 65 * logBracket Q) ^ m *
        ∑ n ∈ Finset.Icc 1 M, (truncDivisor n Q : ℝ) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      have := norm_blockWeight_hbIndex_le Q hn0
      linarith) m
  have hC1 : 0 ≤ (32 * Real.exp 65 * logBracket Q) ^ m := by positivity
  rw [one_div, inv_mul_le_iff₀ hM0]
  refine hpt.trans ?_
  have hexp : ∀ e : ℕ, e ≤ 2 ^ m + m → logBracket Q ^ e ≤ logBracket Q ^ (2 ^ m + m) :=
    fun e he => pow_le_pow_right₀ hL1 he
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rcases le_or_gt 8 Q with h8 | h8
  · have hτ := hCm Q M h8
    calc (32 * Real.exp 65 * logBracket Q) ^ m * ∑ n ∈ Finset.Icc 1 M, (truncDivisor n Q : ℝ) ^ m
        ≤ (32 * Real.exp 65 * logBracket Q) ^ m * (Cm * M * logBracket Q ^ (2 ^ m - 1)) := by
          gcongr
      _ = (32 * Real.exp 65) ^ m * Cm * logBracket Q ^ (m + (2 ^ m - 1)) * M := by
          rw [mul_pow, pow_add]; ring
      _ ≤ (32 * Real.exp 65) ^ m * Cm * logBracket Q ^ (2 ^ m + m) * M := by
          have := hexp (m + (2 ^ m - 1)) (by omega)
          gcongr
      _ ≤ (32 * Real.exp 65) ^ m * (Cm + 7 ^ m) * logBracket Q ^ (2 ^ m + m) * M := by
          have : (0 : ℝ) ≤ 7 ^ m := by positivity
          gcongr
          linarith
      _ = M * ((32 * Real.exp 65) ^ m * (Cm + 7 ^ m) * logBracket Q ^ (2 ^ m + m)) := by ring
  · have hτ : ∑ n ∈ Finset.Icc 1 M, (truncDivisor n Q : ℝ) ^ m ≤ 7 ^ m * M := by
      calc ∑ n ∈ Finset.Icc 1 M, (truncDivisor n Q : ℝ) ^ m
          ≤ ∑ _n ∈ Finset.Icc 1 M, (7 : ℝ) ^ m := by
            refine Finset.sum_le_sum fun n _ => ?_
            have : (truncDivisor n Q : ℝ) ≤ 7 := by exact_mod_cast truncDivisor_le_seven h8 n
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) this m
        _ = 7 ^ m * M := by simp [mul_comm]
    calc (32 * Real.exp 65 * logBracket Q) ^ m * ∑ n ∈ Finset.Icc 1 M, (truncDivisor n Q : ℝ) ^ m
        ≤ (32 * Real.exp 65 * logBracket Q) ^ m * (7 ^ m * M) := by gcongr
      _ = (32 * Real.exp 65) ^ m * 7 ^ m * logBracket Q ^ m * M := by rw [mul_pow]; ring
      _ ≤ (32 * Real.exp 65) ^ m * 7 ^ m * logBracket Q ^ (2 ^ m + m) * M := by
          have := hexp m (by omega)
          gcongr
      _ ≤ (32 * Real.exp 65) ^ m * (Cm + 7 ^ m) * logBracket Q ^ (2 ^ m + m) * M := by
          gcongr
          linarith
      _ = M * ((32 * Real.exp 65) ^ m * (Cm + 7 ^ m) * logBracket Q ^ (2 ^ m + m)) := by ring

end PrimeCarleson.Proof.KMTT
