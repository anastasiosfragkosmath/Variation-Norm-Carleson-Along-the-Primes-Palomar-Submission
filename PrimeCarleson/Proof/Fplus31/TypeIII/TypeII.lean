module

public import PrimeCarleson.Proof.Fplus31.TypeIII.Blocks
public import PrimeCarleson.Proof.Fplus31.TypeIII.BilinearCS
public import PrimeCarleson.Proof.Fplus31.TypeIII.Divisor

/-!
# Type II correlation: a large four-fold sum (Leng23 Proposition 5.1, third bullet)

Part of the Vaughan decomposition in the proof of [F+] Proposition 3.1 (Leng23
`p:type1type2correlation`, `Final_Version.tex` L1096-L1110, with TT21 Proposition 7.2
arXiv:2107.02158v4 TeX (`orthogonality.tex`) L249-L300).

If a bilinear sum `∑_{c ≤ D} ∑_{w ≤ D} a_c b_w f(c w)` with `|a_c| ≤ A` and divisor-bounded
`|b_w| ≤ τ(w)` correlates with a function `f` bounded by `1` and supported on `[1, N]` at the level
`ξ`, where `a_c ≠ 0 ⇒ c³ > N` and `b_w ≠ 0 ⇒ w³ > N`, then there are `L, M` with
`N^{1/3} < L, M ≤ N^{2/3}`, `L M < 4 N`, `L M ≥ ξ/(J² A Λ²)` and
`fourFold f (L/2, L] (M/2, M] ≥ (ξ/J²)⁴ / (16 A⁴ Λ⁶ N²)`, where `Λ = 1 + log N` and
`J = ⌊log₂ D⌋ + 1`.  The lower bound `L M ≥ δ N` is not an extra hypothesis (Leng's
`n ∈ [δ N, N]` restriction): it follows from the four-fold bound and the trivial upper bound
`fourFold ≤ (L M)²`.

* `typeII_extract`: the statement above (Cauchy–Schwarz twice, then the second divisor moment
  `∑_{w ≤ M} τ(w)² ≤ M (1 + log M)³` of `Divisor.lean`).
-/

@[expose] public noncomputable section

open Finset
open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The dyadic block `(L/2, L]` lies in `[1, L]`. -/
theorem dyadicBlock_subset_Icc (L : ℕ) : dyadicBlock L ⊆ Icc 1 L := by
  intro d hd
  rw [dyadicBlock, Finset.mem_Ioc] at hd
  rw [Finset.mem_Icc]
  omega

/-- **Type II extraction** (Leng23 Proposition 5.1, third bullet). -/
theorem typeII_extract (f : ℕ → ℂ) (N D : ℕ) (hD : 1 ≤ D) (hDN : D ^ 3 ≤ N ^ 2)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hf0 : ∀ n, N < n → f n = 0) (a b : ℕ → ℂ) {A : ℝ} (hA0 : 0 < A)
    (hA : ∀ c ∈ Icc 1 D, ‖a c‖ ≤ A) (hb : ∀ w ∈ Icc 1 D, ‖b w‖ ≤ (w.divisors.card : ℝ))
    (ha0 : ∀ c, a c ≠ 0 → N < c ^ 3) (hb0 : ∀ w, b w ≠ 0 → N < w ^ 3) {ξ : ℝ} (hξ : 0 < ξ)
    (h : ξ ≤ ‖∑ c ∈ Icc 1 D, ∑ w ∈ Icc 1 D, a c * b w * f (c * w)‖) :
    ∃ L M : ℕ, N < L ^ 3 ∧ L ^ 3 ≤ N ^ 2 ∧ N < M ^ 3 ∧ M ^ 3 ≤ N ^ 2 ∧
      ξ / (((Nat.log 2 D + 1 : ℕ) : ℝ) ^ 2 * A * (1 + Real.log N) ^ 2) ≤ (L : ℝ) * M ∧
      (L : ℝ) * M < 4 * N ∧
      (ξ / ((Nat.log 2 D + 1 : ℕ) : ℝ) ^ 2) ^ 4 / (16 * A ^ 4 * (1 + Real.log N) ^ 6 * (N : ℝ) ^ 2)
        ≤ fourFold f (dyadicBlock L) (dyadicBlock M) := by
  have hN1 : 1 ≤ N := by
    by_contra hN0
    have : N = 0 := by omega
    subst this
    have : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ hD
    simp at hDN
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hDN' : D ≤ N :=
    (Nat.pow_le_pow_iff_left (by norm_num : 3 ≠ 0)).mp
      (hDN.trans (Nat.pow_le_pow_right hN1 (by norm_num)))
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  set Λ : ℝ := 1 + Real.log N with hΛ
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛpos : 0 < Λ := by linarith
  set J : ℝ := ((Nat.log 2 D + 1 : ℕ) : ℝ) with hJ
  have hJpos : 0 < J := by positivity
  set ξb : ℝ := ξ / J ^ 2 with hξb
  have hξbpos : 0 < ξb := by positivity
  obtain ⟨i, -, j, -, hij⟩ := exists_block_pair_norm_ge D (fun c w => a c * b w * f (c * w)) h
  set L := blockTop D i with hL
  set M := blockTop D j with hM
  set Bi := blockSet D i with hBi
  set Bj := blockSet D j with hBj
  have hBiL : Bi ⊆ dyadicBlock L := blockSet_subset_dyadic D i
  have hBjM : Bj ⊆ dyadicBlock M := blockSet_subset_dyadic D j
  -- a nonzero term
  obtain ⟨c, hc, w, hw, hne⟩ : ∃ c ∈ Bi, ∃ w ∈ Bj, a c * b w * f (c * w) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∑ c ∈ Bi, ∑ w ∈ Bj, a c * b w * f (c * w) = 0 :=
      Finset.sum_eq_zero fun c hc => Finset.sum_eq_zero fun w hw => hcon c hc w hw
    rw [this, norm_zero] at hij
    linarith
  have hca : a c ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hwb : b w ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hfcw : f (c * w) ≠ 0 := right_ne_zero_of_mul hne
  have hcw : c * w ≤ N := by
    by_contra hlt
    exact hfcw (hf0 _ (not_le.mp hlt))
  have hcN : N < c ^ 3 := ha0 c hca
  have hwN : N < w ^ 3 := hb0 w hwb
  have hcL := mem_dyadicBlock.mp (hBiL hc)
  have hwM := mem_dyadicBlock.mp (hBjM hw)
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp (blockSet_subset D i hc)).1
  have hw1 : 1 ≤ w := (Finset.mem_Icc.mp (blockSet_subset D j hw)).1
  have hcLn : c ≤ L := by exact_mod_cast hcL.2
  have hwMn : w ≤ M := by exact_mod_cast hwM.2
  have hL1 : 1 ≤ L := hc1.trans hcLn
  have hM1 : 1 ≤ M := hw1.trans hwMn
  have hLD : L ≤ D := blockTop_le D i
  have hMD : M ≤ D := blockTop_le D j
  have hL3 : L ^ 3 ≤ N ^ 2 := (Nat.pow_le_pow_left hLD 3).trans hDN
  have hM3 : M ^ 3 ≤ N ^ 2 := (Nat.pow_le_pow_left hMD 3).trans hDN
  have hN3L : N < L ^ 3 := hcN.trans_le (Nat.pow_le_pow_left hcLn 3)
  have hN3M : N < M ^ 3 := hwN.trans_le (Nat.pow_le_pow_left hwMn 3)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hLM4 : (L : ℝ) * M < 4 * N := by
    have h1 : (L : ℝ) < 2 * c := by linarith [hcL.1]
    have h2 : (M : ℝ) < 2 * w := by linarith [hwM.1]
    have h3 : (L : ℝ) * M < 2 * c * (2 * w) :=
      mul_lt_mul'' h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h4 : ((c * w : ℕ) : ℝ) ≤ N := by exact_mod_cast hcw
    push_cast at h4
    nlinarith
  -- the size bounds
  have hcardBi : (Bi.card : ℝ) ≤ L := by
    exact_mod_cast (Finset.card_le_card hBiL).trans (card_dyadicBlock_le L)
  have hcardBj : (Bj.card : ℝ) ≤ M := by
    exact_mod_cast (Finset.card_le_card hBjM).trans (card_dyadicBlock_le M)
  have hX : ∑ c ∈ Bi, ‖a c‖ ^ 2 ≤ A ^ 2 * L := by
    calc ∑ c ∈ Bi, ‖a c‖ ^ 2 ≤ ∑ _c ∈ Bi, A ^ 2 := by
          refine Finset.sum_le_sum fun c hc => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (hA c (blockSet_subset D i hc)) 2
      _ = Bi.card * A ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ L * A ^ 2 := mul_le_mul_of_nonneg_right hcardBi (sq_nonneg _)
      _ = A ^ 2 * L := by ring
  have hlogM : Real.log M ≤ Real.log N :=
    Real.log_le_log hMpos (by exact_mod_cast hMD.trans hDN')
  have hY : ∑ w ∈ Bj, ‖b w‖ ^ 2 ≤ M * Λ ^ 3 := by
    calc ∑ w ∈ Bj, ‖b w‖ ^ 2 ≤ ∑ w ∈ Bj, ((w.divisors.card : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum fun w hw => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (hb w (blockSet_subset D j hw)) 2
      _ ≤ ∑ w ∈ Icc 1 M, ((w.divisors.card : ℝ)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (hBjM.trans (dyadicBlock_subset_Icc M))
            fun _ _ _ => sq_nonneg _
      _ ≤ M * (1 + Real.log M) ^ 3 := sum_Icc_card_divisors_sq_le M
      _ ≤ M * Λ ^ 3 := by
          have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by rw [hΛ]; linarith) 3) (Nat.cast_nonneg _)
  have hF : fourFold f Bi Bj ≤ ((L : ℝ) * M) ^ 2 := by
    refine (fourFold_le f hf Bi Bj).trans ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    exact mul_le_mul hcardBi hcardBj (Nat.cast_nonneg _) hLpos.le
  have hFnn : 0 ≤ fourFold f Bi Bj := fourFold_nonneg f Bi Bj
  -- Cauchy–Schwarz
  have hcs := bilinear_cs f Bi Bj a b
  have hfour : ξb ^ 4 ≤ A ^ 4 * Λ ^ 6 * ((L : ℝ) * M) ^ 2 * fourFold f Bi Bj := by
    calc ξb ^ 4 ≤ ‖∑ c ∈ Bi, ∑ w ∈ Bj, a c * b w * f (c * w)‖ ^ 4 :=
          pow_le_pow_left₀ hξbpos.le hij 4
      _ ≤ _ := hcs
      _ ≤ ((A ^ 2 * L) ^ 2 * (M * Λ ^ 3) ^ 2) * fourFold f Bi Bj := by
          refine mul_le_mul_of_nonneg_right ?_ hFnn
          refine mul_le_mul (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) hX 2)
            (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) hY 2)
            (by positivity) (by positivity)
      _ = _ := by ring
  refine ⟨L, M, hN3L, hL3, hN3M, hM3, ?_, hLM4, ?_⟩
  · -- lower bound on L * M
    have h1 : ξb ^ 4 ≤ (A * Λ ^ 2 * ((L : ℝ) * M)) ^ 4 := by
      calc ξb ^ 4 ≤ A ^ 4 * Λ ^ 6 * ((L : ℝ) * M) ^ 2 * ((L : ℝ) * M) ^ 2 :=
            hfour.trans (mul_le_mul_of_nonneg_left hF (by positivity))
        _ ≤ A ^ 4 * Λ ^ 8 * ((L : ℝ) * M) ^ 4 := by
            have : Λ ^ 6 ≤ Λ ^ 8 := pow_le_pow_right₀ hΛ1 (by norm_num)
            have h2 : ((L : ℝ) * M) ^ 2 * ((L : ℝ) * M) ^ 2 = ((L : ℝ) * M) ^ 4 := by ring
            calc A ^ 4 * Λ ^ 6 * ((L : ℝ) * M) ^ 2 * ((L : ℝ) * M) ^ 2
                = A ^ 4 * Λ ^ 6 * ((L : ℝ) * M) ^ 4 := by ring
              _ ≤ A ^ 4 * Λ ^ 8 * ((L : ℝ) * M) ^ 4 := by gcongr
        _ = (A * Λ ^ 2 * ((L : ℝ) * M)) ^ 4 := by ring
    have h2 : ξb ≤ A * Λ ^ 2 * ((L : ℝ) * M) :=
      le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    rw [hξb, div_le_iff₀ (by positivity)] at h2
    rw [div_le_iff₀ (by positivity)]
    linarith
  · -- the four-fold bound
    have hmono : fourFold f Bi Bj ≤ fourFold f (dyadicBlock L) (dyadicBlock M) :=
      (fourFold_mono_left f hBiL Bj).trans (fourFold_mono_right f _ hBjM)
    refine le_trans ?_ hmono
    rw [div_le_iff₀ (by positivity)]
    have hLM2 : ((L : ℝ) * M) ^ 2 ≤ 16 * (N : ℝ) ^ 2 := by
      have : (L : ℝ) * M ≤ 4 * N := hLM4.le
      calc ((L : ℝ) * M) ^ 2 ≤ (4 * (N : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
        _ = 16 * (N : ℝ) ^ 2 := by ring
    calc ξb ^ 4 ≤ A ^ 4 * Λ ^ 6 * ((L : ℝ) * M) ^ 2 * fourFold f Bi Bj := hfour
      _ ≤ A ^ 4 * Λ ^ 6 * (16 * (N : ℝ) ^ 2) * fourFold f Bi Bj := by
          refine mul_le_mul_of_nonneg_right ?_ hFnn
          exact mul_le_mul_of_nonneg_left hLM2 (by positivity)
      _ = fourFold f Bi Bj * (16 * A ^ 4 * Λ ^ 6 * (N : ℝ) ^ 2) := by ring

end PrimeCarleson.Proof.Fplus31
