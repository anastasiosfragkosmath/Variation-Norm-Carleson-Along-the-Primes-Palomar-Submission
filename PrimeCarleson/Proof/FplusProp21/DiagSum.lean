module

public import PrimeCarleson.Proof.FplusProp21.Arith
public import Mathlib.Analysis.PSeries

/-!
# The diagonal sum: `S_0 ≲_ε Q^{-3+ε}`

Source: [F+] `expansion-u3-norm-2`, L788–L791 ([F+] TeX; proof
L847–L911), the claim of the proof of [F+] Proposition 2.1, for every finite set `B` of denominators
in `[Q/2, Q]`:

1. every tuple contributes at most `16^{ω(r)} r^{-2} R^{-1/4} ≤ (4/Q²) 16^{ω(r)} r^{-2}`
   (`prod_muSqDivTotient_mul_card_le`, `R = ∏ q_ω ≥ (Q/2)⁸`);
2. the tuples with `lcm(q_ω) = r` number at most `τ(r)⁸`, and `Q/2 ≤ r ≤ Q⁸`;
3. `τ(r)⁸ 16^{ω(r)} ≤ τ(r)^{12} ≤ C_δ^{12} Q^{96 δ}` (`2^{ω(r)} ≤ τ(r)` and the divisor bound
   `Goal0.exists_card_divisors_le_rpow`);
4. `∑_{r ≥ Q/2} r^{-2} ≤ 4/Q` (`sum_Ioo_inv_sq_le`).

This replaces the source's dyadic decomposition of `r` ([F+] L889–L911) by a direct estimate.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.FplusProp21

/-- `2^{ω(n)} ≤ τ(n)`. -/
theorem two_pow_card_primeFactors_le {n : ℕ} (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn.ne']
  refine pow_card_le_prod _ _ _ fun p hp => ?_
  have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn.ne'
    (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- `∑_{N₁ ≤ r ≤ N₂} r^{-2} ≤ 2 / N₁` for `N₁ ≥ 1`. -/
theorem sum_Icc_inv_sq_le {N₁ : ℕ} (hN₁ : 1 ≤ N₁) (N₂ : ℕ) :
    ∑ r ∈ Icc N₁ N₂, ((r : ℝ) ^ 2)⁻¹ ≤ 2 / N₁ := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) (N₁ - 1) (N₂ + 1)
  have hI : Ioo (N₁ - 1) (N₂ + 1) = Icc N₁ N₂ := by
    ext r
    simp only [mem_Ioo, mem_Icc]
    omega
  rw [hI] at h
  have hc : ((N₁ - 1 : ℕ) : ℝ) + 1 = N₁ := by
    rw [Nat.cast_sub hN₁]
    ring
  rwa [hc] at h

/-- The number of denominator tuples in `B⁸` with `lcm = r` is at most `τ(r)⁸`. -/
theorem card_filter_cubeLcm_eq_le (B : Finset ℕ) {r : ℕ} (hr : r ≠ 0) :
    ((Fintype.piFinset fun _ : Cube => B).filter (fun q => cubeLcm q = r)).card ≤
      r.divisors.card ^ 8 := by
  classical
  calc ((Fintype.piFinset fun _ : Cube => B).filter (fun q => cubeLcm q = r)).card
      ≤ (Fintype.piFinset fun _ : Cube => r.divisors).card := by
        refine card_le_card fun q hq => ?_
        rw [mem_filter] at hq
        rw [Fintype.mem_piFinset]
        intro ω
        rw [Nat.mem_divisors]
        exact ⟨hq.2 ▸ dvd_cubeLcm q ω, hr⟩
    _ = r.divisors.card ^ 8 := by
        rw [Fintype.card_piFinset, prod_const]
        simp

/-- **The arithmetic core** (Source: [F+] `expansion-u3-norm-2`, L788–L791): for every `ε > 0` there
is `C_ε` with `∑_{(q_ω, a_ω) : L_j ∈ ℤ} ∏_ω μ²(q_ω)/φ(q_ω) ≤ C_ε Q^{-3+ε}` for all `Q ≥ 1` and every
finite set `B ⊆ [Q/2, Q]` of denominators. -/
theorem exists_diagSum_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ B : Finset ℕ,
      (∀ q ∈ B, Q / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q) → diagSum B ≤ C * Q ^ (-3 + ε) := by
  classical
  obtain ⟨C₀, hC₀, hdiv⟩ := Goal0.exists_card_divisors_le_rpow (δ := ε / 96) (by positivity)
  refine ⟨16 * C₀ ^ 12, by positivity, fun Q hQ B hB => ?_⟩
  have hQpos : 0 < Q := by linarith
  have hB0 : ∀ q ∈ B, q ≠ 0 := by
    intro q hq h
    have := (hB q hq).1
    rw [h, Nat.cast_zero] at this
    linarith
  set N₁ : ℕ := ⌈Q / 2⌉₊ with hN₁
  set N₂ : ℕ := ⌊Q ^ 8⌋₊ with hN₂
  have hN₁pos : 1 ≤ N₁ := Nat.one_le_iff_ne_zero.2 (by
    rw [hN₁, Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have hN₁Q : Q / 2 ≤ N₁ := Nat.le_ceil _
  set G : ℕ → ℝ := fun r => 16 ^ r.primeFactors.card / (r : ℝ) ^ 2 with hG
  have hG0 : ∀ r, 0 ≤ G r := fun r => by positivity
  -- bounds for a tuple in `B⁸`
  have hqB : ∀ q ∈ Fintype.piFinset (fun _ : Cube => B), ∀ ω,
      Q / 2 ≤ (q ω : ℝ) ∧ (q ω : ℝ) ≤ Q := fun q hq ω =>
    hB _ (Fintype.mem_piFinset.1 hq ω)
  have hRlow : ∀ q ∈ Fintype.piFinset (fun _ : Cube => B),
      (Q / 2) ^ 8 ≤ ((∏ ω, q ω : ℕ) : ℝ) := by
    intro q hq
    push_cast
    calc (Q / 2) ^ 8 = ∏ _ω : Cube, Q / 2 := by simp [prod_const, div_pow]
      _ ≤ ∏ ω, (q ω : ℝ) :=
          prod_le_prod₀ (fun _ _ => by positivity) (fun ω _ => (hqB q hq ω).1)
  have hRup : ∀ q ∈ Fintype.piFinset (fun _ : Cube => B), ((∏ ω, q ω : ℕ) : ℝ) ≤ Q ^ 8 := by
    intro q hq
    push_cast
    calc ∏ ω, (q ω : ℝ) ≤ ∏ _ω : Cube, Q :=
          prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun ω _ => (hqB q hq ω).2)
      _ = Q ^ 8 := by simp
  -- step 1: one tuple
  have hstep1 : diagSum B ≤ ∑ q ∈ Fintype.piFinset (fun _ : Cube => B),
      4 / Q ^ 2 * G (cubeLcm q) := by
    refine (diagSum_le_sum_numerators B hB0).trans (sum_le_sum fun q hq => ?_)
    by_cases hsq : ∀ ω, Squarefree (q ω)
    · refine (prod_muSqDivTotient_mul_card_le hsq).trans ?_
      have hr0 : (0 : ℝ) < cubeLcm q := by
        exact_mod_cast Nat.pos_of_ne_zero (cubeLcm_ne_zero fun ω => (hsq ω).ne_zero)
      have hroot : (Q / 2) ^ 2 ≤ ((∏ ω, q ω : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
        calc (Q / 2) ^ 2 = (((Q / 2) ^ 2) ^ 4) ^ ((1 : ℝ) / 4) :=
              (rpow_quarter_pow_four (by positivity)).symm
          _ ≤ ((∏ ω, q ω : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
              refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
              rw [← pow_mul]
              exact hRlow q hq
      calc (16 : ℝ) ^ (cubeLcm q).primeFactors.card /
            ((cubeLcm q : ℝ) ^ 2 * ((∏ ω, q ω : ℕ) : ℝ) ^ ((1 : ℝ) / 4))
          ≤ (16 : ℝ) ^ (cubeLcm q).primeFactors.card / ((cubeLcm q : ℝ) ^ 2 * (Q / 2) ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hroot (by positivity))
        _ = 4 / Q ^ 2 * G (cubeLcm q) := by
            simp only [hG]
            field_simp
            ring
    · push Not at hsq
      obtain ⟨ω, hω⟩ := hsq
      have h0 : ∏ ω, muSqDivTotient (q ω) = 0 := prod_eq_zero (mem_univ ω) (by
        simp [muSqDivTotient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hω])
      rw [h0, zero_mul]
      exact mul_nonneg (by positivity) (hG0 _)
  -- step 2: group the tuples by `r = lcm(q_ω)`
  have hmaps : ∀ q ∈ Fintype.piFinset (fun _ : Cube => B), cubeLcm q ∈ Icc N₁ N₂ := by
    intro q hq
    have hq0 : ∀ ω, q ω ≠ 0 := fun ω => hB0 _ (Fintype.mem_piFinset.1 hq ω)
    have hr0 := cubeLcm_ne_zero hq0
    rw [mem_Icc]
    constructor
    · rw [hN₁, Nat.ceil_le]
      refine (hqB q hq (fun _ => 0)).1.trans ?_
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) (dvd_cubeLcm q _)
    · rw [hN₂]
      refine Nat.le_floor ((?_ : (cubeLcm q : ℝ) ≤ ((∏ ω, q ω : ℕ) : ℝ)).trans (hRup q hq))
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (prod_ne_zero_iff.2 fun ω _ => hq0 ω))
        (cubeLcm_dvd_prod q)
  have hstep2 : ∑ q ∈ Fintype.piFinset (fun _ : Cube => B), G (cubeLcm q) ≤
      ∑ r ∈ Icc N₁ N₂, (r.divisors.card : ℝ) ^ 8 * G r := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_le_sum fun r hr => ?_
    have hr0 : r ≠ 0 := by
      rw [mem_Icc] at hr
      omega
    rw [sum_congr rfl (g := fun _ => G r) (fun q hq => by rw [(mem_filter.1 hq).2]), sum_const,
      nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hG0 r)
    exact_mod_cast card_filter_cubeLcm_eq_le B hr0
  -- step 3: the divisor bound
  have hQε : ((Q ^ 8) ^ (ε / 96)) ^ 12 = Q ^ ε := by
    rw [← Real.rpow_natCast ((Q ^ 8) ^ (ε / 96)) 12, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast Q 8, ← Real.rpow_mul hQpos.le]
    congr 1
    push_cast
    ring
  have hstep3 : ∀ r ∈ Icc N₁ N₂, (r.divisors.card : ℝ) ^ 8 * G r ≤
      C₀ ^ 12 * Q ^ ε * ((r : ℝ) ^ 2)⁻¹ := by
    intro r hr
    rw [mem_Icc] at hr
    have hrpos : 0 < r := by omega
    have hrQ : (r : ℝ) ≤ Q ^ 8 := by
      have := Nat.floor_le (a := Q ^ 8) (by positivity)
      exact (Nat.cast_le.2 hr.2).trans this
    have hτ : (r.divisors.card : ℝ) ≤ C₀ * (Q ^ 8) ^ (ε / 96) :=
      (hdiv r hrpos).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hrQ (by positivity)) (by positivity))
    have h16 : (16 : ℝ) ^ r.primeFactors.card ≤ (r.divisors.card : ℝ) ^ 4 := by
      have := two_pow_card_primeFactors_le hrpos
      have h' : (2 : ℝ) ^ r.primeFactors.card ≤ (r.divisors.card : ℝ) := by
        exact_mod_cast this
      calc (16 : ℝ) ^ r.primeFactors.card = ((2 : ℝ) ^ r.primeFactors.card) ^ 4 := by
            rw [← pow_mul, mul_comm, pow_mul]
            norm_num
        _ ≤ (r.divisors.card : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) h' 4
    simp only [hG]
    rw [div_eq_mul_inv, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (r.divisors.card : ℝ) ^ 8 * 16 ^ r.primeFactors.card
        ≤ (r.divisors.card : ℝ) ^ 8 * (r.divisors.card : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left h16 (by positivity)
      _ = (r.divisors.card : ℝ) ^ 12 := by ring
      _ ≤ (C₀ * (Q ^ 8) ^ (ε / 96)) ^ 12 := pow_le_pow_left₀ (by positivity) hτ 12
      _ = C₀ ^ 12 * Q ^ ε := by rw [mul_pow, hQε]
  -- step 4: assemble
  have hsum : ∑ r ∈ Icc N₁ N₂, ((r : ℝ) ^ 2)⁻¹ ≤ 4 / Q := by
    refine (sum_Icc_inv_sq_le hN₁pos N₂).trans ?_
    rw [div_le_div_iff₀ (by exact_mod_cast hN₁pos) hQpos]
    linarith
  have hQ3 : Q ^ (-3 + ε) = Q ^ ε / Q ^ 3 := by
    rw [Real.rpow_add hQpos, Real.rpow_neg hQpos.le, ← Real.rpow_natCast Q 3]
    · push_cast
      ring
  calc diagSum B ≤ ∑ q ∈ Fintype.piFinset (fun _ : Cube => B), 4 / Q ^ 2 * G (cubeLcm q) :=
        hstep1
    _ = 4 / Q ^ 2 * ∑ q ∈ Fintype.piFinset (fun _ : Cube => B), G (cubeLcm q) := by
        rw [mul_sum]
    _ ≤ 4 / Q ^ 2 * ∑ r ∈ Icc N₁ N₂, C₀ ^ 12 * Q ^ ε * ((r : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (hstep2.trans (sum_le_sum hstep3)) (by positivity)
    _ = 4 / Q ^ 2 * (C₀ ^ 12 * Q ^ ε) * ∑ r ∈ Icc N₁ N₂, ((r : ℝ) ^ 2)⁻¹ := by
        rw [← mul_sum]
        ring
    _ ≤ 4 / Q ^ 2 * (C₀ ^ 12 * Q ^ ε) * (4 / Q) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 16 * C₀ ^ 12 * Q ^ (-3 + ε) := by
        rw [hQ3]
        field_simp
        ring

end PrimeCarleson.Proof.FplusProp21
