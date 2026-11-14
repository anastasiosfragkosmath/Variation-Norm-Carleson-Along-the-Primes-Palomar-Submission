module

public import PrimeCarleson.Proof.Fplus31.Comparison.L2

/-!
# Cramér–Heath-Brown comparison, step 6: the quantitative bounds for `D₂`

The numerical part of piece `D₂` of the comparison of the Cramér model with the Heath-Brown model,
for `L = (log N)^{1/10} ≥ 40`, `N = e^{L^{10}}`, `2 ≤ w ≤ 2 e^L`, `e^{L^{10}/21} ≤ 2R`,
`R ≤ e^{L^{10}/21}` (so `R ≈ N^{1/21}`):

* `tailSum_le`: Rankin's trick with `σ = log 2/(L + 1)` gives
  `∑_{q ∣ P(w), q > R} 1/φ(q) ≤ e^{-L-2}`;
* `sum_cramerModel_sub_le`: Brun's pure sieve with `k + 1 ≈ L²` gives
  `(P/φ(P)) |∑_{n ≤ N} Λ_{C,w}(n) - N| ≤ N e^{-L-2}`;
* `avg_sq_tail_le`: `N⁻¹ ∑_{n ≤ N} |D₂(n)|² ≤ e^{-L}`.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open PrimeCarleson

/-- For `L ≥ 40`: `10^6 L² ≤ L^10`. -/
theorem ten_pow_six_mul_sq_le {L : ℝ} (hL : 40 ≤ L) : 10 ^ 6 * L ^ 2 ≤ L ^ 10 := by
  have h8 : (40 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL 8
  have : L ^ 10 = L ^ 2 * L ^ 8 := by ring
  rw [this]
  have h2 : 0 ≤ L ^ 2 := by positivity
  linarith [mul_le_mul_of_nonneg_left h8 h2]

/-- For `L ≥ 40`: `10^6 L³ ≤ L^10`. -/
theorem ten_pow_six_mul_cube_le {L : ℝ} (hL : 40 ≤ L) : 10 ^ 6 * L ^ 3 ≤ L ^ 10 := by
  have h7 : (40 : ℝ) ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL 7
  have : L ^ 10 = L ^ 3 * L ^ 7 := by ring
  rw [this]
  have h2 : 0 ≤ L ^ 3 := by positivity
  linarith [mul_le_mul_of_nonneg_left h7 h2]

/-- `0 < log w ≤ L + 1` when `2 ≤ w ≤ 2 e^L`. -/
theorem log_le_of_le_two_mul_exp {w : ℕ} {L : ℝ} (hw2 : 2 ≤ w) (hwL : (w : ℝ) ≤ 2 * Real.exp L) :
    0 < Real.log w ∧ Real.log w ≤ L + 1 := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  refine ⟨Real.log_pos (by exact_mod_cast hw2), ?_⟩
  have h1 : Real.log w ≤ Real.log (2 * Real.exp L) := Real.log_le_log hw0 hwL
  rw [Real.log_mul (by norm_num) (Real.exp_pos L).ne', Real.log_exp] at h1
  have := Real.log_two_lt_d9
  linarith

/-- `P(w)/φ(P(w)) ≥ 1`. -/
theorem one_le_primorialBelow_div_totient (w : ℕ) :
    1 ≤ (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) := by
  have hpos : (0 : ℝ) < Nat.totient (primorialBelow w) := by
    exact_mod_cast Nat.totient_pos.2 (primorialBelow_pos w)
  rw [one_le_div hpos]
  exact_mod_cast Nat.totient_le _

/-- `P(w)/φ(P(w)) ≤ e^{L+5}` when `2 ≤ w ≤ 2 e^L`. -/
theorem primorialBelow_div_totient_le_exp {w : ℕ} {L : ℝ} (hw2 : 2 ≤ w)
    (hwL : (w : ℝ) ≤ 2 * Real.exp L) :
    (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) ≤ Real.exp (L + 5) := by
  obtain ⟨-, hlog⟩ := log_le_of_le_two_mul_exp hw2 hwL
  refine (primorialBelow_div_totient_le w hw2).trans ?_
  have h1 : L + 1 ≤ Real.exp L := Real.add_one_le_exp L
  rw [show L + 5 = 5 + L by ring, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (hlog.trans h1) (Real.exp_pos 5).le

/-- **The Rankin tail is tiny**: `∑_{q ∣ P(w), q > R} 1/φ(q) ≤ e^{-L-2}`, for `L ≥ 40`,
`2 ≤ w ≤ 2 e^L` and `e^{L^{10}/21} ≤ 2R`. -/
theorem tailSum_le {w R : ℕ} {L : ℝ} (hL : 40 ≤ L) (hw2 : 2 ≤ w)
    (hwL : (w : ℝ) ≤ 2 * Real.exp L) (hR0 : 0 < R)
    (hRlo : Real.exp (L ^ 10 / 21) ≤ 2 * R) : tailSum w R ≤ Real.exp (-L - 2) := by
  obtain ⟨hlog0, hlog⟩ := log_le_of_le_two_mul_exp hw2 hwL
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR0
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  set σ : ℝ := Real.log 2 / (L + 1) with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hp2 : ∀ p ∈ Nat.primesBelow w, (p : ℝ) ^ σ ≤ 2 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).pos
    have hpw : (p : ℝ) ≤ w := by exact_mod_cast (Nat.lt_of_mem_primesBelow hp).le
    have hw0 : (0 : ℝ) < w := by linarith [hp0, hpw]
    calc (p : ℝ) ^ σ ≤ (w : ℝ) ^ σ := Real.rpow_le_rpow hp0.le hpw hσ0
      _ = Real.exp (Real.log w * σ) := Real.rpow_def_of_pos hw0 σ
      _ ≤ Real.exp (Real.log 2) := by
          refine Real.exp_le_exp.2 ?_
          rw [hσ, ← mul_div_assoc, div_le_iff₀ (by linarith only [hL])]
          linarith only [mul_le_mul_of_nonneg_left hlog (by linarith only [hlog2] :
            (0 : ℝ) ≤ Real.log 2)]
      _ = 2 := Real.exp_log (by norm_num)
  have htail : tailSum w R ≤ (R : ℝ) ^ (-σ) *
      ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ)) ^ 2 :=
    sum_tail_inv_totient_le_sq w hR0 hσ0 hp2
  have hS := primorialBelow_div_totient_le_exp hw2 hwL
  have hS0 := one_le_primorialBelow_div_totient w
  have hSsq : ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ)) ^ 2 ≤
      Real.exp (2 * L + 10) := by
    calc _ ≤ (Real.exp (L + 5)) ^ 2 := pow_le_pow_left₀ (by linarith) hS 2
      _ = Real.exp (2 * L + 10) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  -- the exponent
  have hX := ten_pow_six_mul_sq_le hL
  have hlogR : L ^ 10 / 21 - 1 ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos _) hRlo
    rw [Real.log_exp, Real.log_mul (by norm_num) hR'.ne'] at this
    linarith
  have hσlog : 3 * L + 12 ≤ σ * Real.log R := by
    rw [hσ, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    have hL2 : (40 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
    have h3 : (3 * L + 12) * (L + 1) ≤ 8 * L ^ 2 := by
      have := mul_le_mul_of_nonneg_right hL (by linarith only [hL] : (0 : ℝ) ≤ L)
      linarith only [this, hL, hL2]
    have h4 : 0.69 * (L ^ 10 / 21 - 1) ≤ Real.log 2 * Real.log R := by
      have hlr : 0 ≤ Real.log R := by
        have : (0 : ℝ) ≤ L ^ 10 / 21 - 1 := by linarith only [hX, hL2]
        linarith only [this, hlogR]
      linarith only [mul_nonneg (sub_nonneg.2 hlog2.le) hlr, hlogR]
    linarith only [h3, h4, hX, hL2]
  have hRpow : (R : ℝ) ^ (-σ) ≤ Real.exp (-(3 * L + 12)) := by
    rw [Real.rpow_def_of_pos hR']
    refine Real.exp_le_exp.2 ?_
    linarith only [hσlog]
  calc tailSum w R ≤ (R : ℝ) ^ (-σ) *
        ((primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ)) ^ 2 := htail
    _ ≤ Real.exp (-(3 * L + 12)) * Real.exp (2 * L + 10) :=
        mul_le_mul hRpow hSsq (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-L - 2) := by rw [← Real.exp_add]; ring_nf


/-- **The density of the Cramér model is `1 + O(e^{-L-2}/S)`** (Brun's pure sieve with
`k + 1 ≈ L²`): `(P/φ(P)) |∑_{n ≤ N} Λ_{C,w}(n) - N| ≤ N e^{-L-2}`. -/
theorem sum_cramerModel_sub_le {N w : ℕ} {L : ℝ} (hL : 40 ≤ L)
    (hN : (N : ℝ) = Real.exp (L ^ 10)) (hw2 : 2 ≤ w) (hwL : (w : ℝ) ≤ 2 * Real.exp L) :
    (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) *
        |∑ n ∈ Icc (1 : ℤ) N, cramerModel w n - (N : ℝ)| ≤ N * Real.exp (-L - 2) := by
  obtain ⟨hlog0, hlog⟩ := log_le_of_le_two_mul_exp hw2 hwL
  set S : ℝ := (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) with hSdef
  have hS : S ≤ Real.exp (L + 5) := primorialBelow_div_totient_le_exp hw2 hwL
  have hS1 : 1 ≤ S := one_le_primorialBelow_div_totient w
  have hX := ten_pow_six_mul_sq_le hL
  set X : ℝ := L ^ 10 with hXdef
  set k : ℕ := ⌊L ^ 2⌋₊ with hk
  have hk1 : L ^ 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk2 : (k : ℝ) ≤ L ^ 2 := Nat.floor_le (by positivity)
  have hbrun := brun_Icc w k N hw2
  rw [← hSdef] at hbrun
  set S' : ℝ := ∑ p ∈ Nat.primesBelow w, (1 : ℝ) / p with hS'
  have hS'0 : 0 ≤ S' := Finset.sum_nonneg fun p _ => by positivity
  have hS'1 : S' ≤ L + 4 := by
    have h1 := PrimeCarleson.Proof.Common.sum_primesBelow_inv_le_log_log hw2
    have h2 : Real.log (Real.log w) ≤ L := by
      have := Real.log_le_log hlog0 hlog
      have h3 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L + 1)
      linarith
    linarith
  have hκ : (1 : ℕ) ≤ k + 1 := Nat.succ_pos k
  -- the factor `S'^κ/κ!`
  have hA : S' ^ (k + 1) / ((k + 1).factorial : ℝ) ≤ Real.exp (-(L ^ 2)) := by
    refine (pow_div_factorial_le hS'0 hκ).trans ?_
    have he : Real.exp 1 < 2.72 := by
      have := Real.exp_one_lt_d9
      linarith
    have hκpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hratio : Real.exp 1 * S' / ((k + 1 : ℕ) : ℝ) ≤ Real.exp (-1) := by
      rw [div_le_iff₀ hκpos, Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos 1)]
      push_cast
      have h1 : Real.exp 1 * Real.exp 1 ≤ 8 := by
        calc Real.exp 1 * Real.exp 1 ≤ 2.72 * 2.72 :=
              mul_le_mul he.le he.le (Real.exp_pos 1).le (by norm_num)
          _ ≤ 8 := by norm_num
      have h3 : Real.exp 1 * S' * Real.exp 1 ≤ 8 * S' :=
        calc Real.exp 1 * S' * Real.exp 1 = (Real.exp 1 * Real.exp 1) * S' := by ring
          _ ≤ 8 * S' := mul_le_mul_of_nonneg_right h1 hS'0
      have h4 : 8 * (L + 4) ≤ L ^ 2 := by nlinarith only [hL]
      linarith only [h3, h4, hS'1, hk1]
    calc (Real.exp 1 * S' / ((k + 1 : ℕ) : ℝ)) ^ (k + 1) ≤ (Real.exp (-1)) ^ (k + 1) :=
          pow_le_pow_left₀ (by positivity) hratio _
      _ = Real.exp (-((k + 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (-(L ^ 2)) := by
          refine Real.exp_le_exp.2 ?_
          push_cast
          linarith
  -- the Brun error
  have hexpS' : Real.exp S' ≤ Real.exp (L + 4) := Real.exp_le_exp.2 hS'1
  have hfirst : 2 * Real.exp S' * S' ^ (k + 1) / ((k + 1).factorial : ℝ) * (N : ℝ) ≤
      2 * Real.exp (L + 4 - L ^ 2) * (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    calc 2 * Real.exp S' * S' ^ (k + 1) / ((k + 1).factorial : ℝ) * (N : ℝ)
        = 2 * Real.exp S' * (S' ^ (k + 1) / ((k + 1).factorial : ℝ)) * (N : ℝ) := by ring
      _ ≤ 2 * Real.exp (L + 4) * Real.exp (-(L ^ 2)) * (N : ℝ) := by
          gcongr
      _ = 2 * Real.exp (L + 4 - L ^ 2) * (N : ℝ) := by
          have : Real.exp (L + 4 - L ^ 2) = Real.exp (L + 4) * Real.exp (-(L ^ 2)) := by
            rw [← Real.exp_add]; ring_nf
          rw [this]; ring
  have hX3 := ten_pow_six_mul_cube_le hL
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL2 : 1600 ≤ L ^ 2 := by nlinarith only [hL]
  have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL0 3
  have h40 : 40 * L ≤ L ^ 2 := by nlinarith only [hL]
  have hsecond : 2 * ((k : ℝ) + 1) * (w : ℝ) ^ (k + 1) ≤ Real.exp (X / 2) := by
    have hw1 : (w : ℝ) ≤ Real.exp (L + 1) := by
      rw [Real.exp_add]
      have : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      calc (w : ℝ) ≤ 2 * Real.exp L := hwL
        _ ≤ Real.exp L * Real.exp 1 := by
            linarith only [mul_le_mul_of_nonneg_left this (Real.exp_pos L).le]
    have hwk : (w : ℝ) ^ (k + 1) ≤ Real.exp ((L + 1) * ((k : ℝ) + 1)) := by
      calc (w : ℝ) ^ (k + 1) ≤ (Real.exp (L + 1)) ^ (k + 1) :=
            pow_le_pow_left₀ (by positivity) hw1 _
        _ = Real.exp ((L + 1) * ((k : ℝ) + 1)) := by
            rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hk2' : 2 * ((k : ℝ) + 1) ≤ Real.exp (2 * L ^ 2 + 1) := by
      have := Real.add_one_le_exp (2 * L ^ 2 + 1)
      linarith
    calc 2 * ((k : ℝ) + 1) * (w : ℝ) ^ (k + 1)
        ≤ Real.exp (2 * L ^ 2 + 1) * Real.exp ((L + 1) * ((k : ℝ) + 1)) :=
          mul_le_mul hk2' hwk (by positivity) (Real.exp_pos _).le
      _ = Real.exp (2 * L ^ 2 + 1 + (L + 1) * ((k : ℝ) + 1)) := by rw [← Real.exp_add]
      _ ≤ Real.exp (X / 2) := by
          refine Real.exp_le_exp.2 ?_
          have h1 : (L + 1) * ((k : ℝ) + 1) ≤ (L + 1) * (L ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          linarith only [h1, hX, hX3, hL2, hL3, h40, hL]
  have hexpX : Real.exp (X / 2) = (N : ℝ) * Real.exp (-(X / 2)) := by
    rw [hN, ← Real.exp_add]; ring_nf
  have hSsq : S * S ≤ Real.exp (2 * L + 10) := by
    calc S * S ≤ Real.exp (L + 5) * Real.exp (L + 5) :=
          mul_le_mul hS hS (by linarith) (Real.exp_pos _).le
      _ = Real.exp (2 * L + 10) := by rw [← Real.exp_add]; ring_nf
  have hN0 : (0 : ℝ) < N := by rw [hN]; exact Real.exp_pos _
  -- assemble
  have h1 : S * |∑ n ∈ Icc (1 : ℤ) N, cramerModel w n - (N : ℝ)| ≤
      S * (S * (2 * Real.exp S' * S' ^ (k + 1) / ((k + 1).factorial : ℝ) * (N : ℝ) +
        2 * ((k : ℝ) + 1) * (w : ℝ) ^ (k + 1))) :=
    mul_le_mul_of_nonneg_left hbrun (by linarith)
  have h2 : S * (S * (2 * Real.exp S' * S' ^ (k + 1) / ((k + 1).factorial : ℝ) * (N : ℝ) +
        2 * ((k : ℝ) + 1) * (w : ℝ) ^ (k + 1))) ≤
      Real.exp (2 * L + 10) * ((N : ℝ) * (2 * Real.exp (L + 4 - L ^ 2) +
        Real.exp (-(X / 2)))) := by
    rw [← mul_assoc]
    refine mul_le_mul hSsq ?_ (by positivity) (Real.exp_pos _).le
    calc 2 * Real.exp S' * S' ^ (k + 1) / ((k + 1).factorial : ℝ) * (N : ℝ) +
          2 * ((k : ℝ) + 1) * (w : ℝ) ^ (k + 1)
        ≤ 2 * Real.exp (L + 4 - L ^ 2) * (N : ℝ) + (N : ℝ) * Real.exp (-(X / 2)) := by
          rw [← hexpX]
          exact add_le_add hfirst hsecond
      _ = _ := by ring
  have h3 : Real.exp (2 * L + 10) * (2 * Real.exp (L + 4 - L ^ 2) + Real.exp (-(X / 2))) ≤
      Real.exp (-L - 2) := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have ha : Real.exp (2 * L + 10) * (2 * Real.exp (L + 4 - L ^ 2)) ≤ Real.exp (-L - 3) := by
      calc Real.exp (2 * L + 10) * (2 * Real.exp (L + 4 - L ^ 2))
          ≤ Real.exp (2 * L + 10) * (Real.exp 1 * Real.exp (L + 4 - L ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le)
              (Real.exp_pos _).le
        _ = Real.exp (3 * L + 15 - L ^ 2) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-L - 3) := by
            refine Real.exp_le_exp.2 ?_
            linarith only [h40, hL]
    have hb : Real.exp (2 * L + 10) * Real.exp (-(X / 2)) ≤ Real.exp (-L - 3) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith only [hX, h40, hL]
    calc Real.exp (2 * L + 10) * (2 * Real.exp (L + 4 - L ^ 2) + Real.exp (-(X / 2)))
        = Real.exp (2 * L + 10) * (2 * Real.exp (L + 4 - L ^ 2)) +
            Real.exp (2 * L + 10) * Real.exp (-(X / 2)) := by ring
      _ ≤ Real.exp (-L - 3) + Real.exp (-L - 3) := add_le_add ha hb
      _ = 2 * Real.exp (-L - 3) := by ring
      _ ≤ Real.exp 1 * Real.exp (-L - 3) :=
          mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
      _ = Real.exp (-L - 2) := by rw [← Real.exp_add]; ring_nf
  calc S * |∑ n ∈ Icc (1 : ℤ) N, cramerModel w n - (N : ℝ)|
      ≤ Real.exp (2 * L + 10) * ((N : ℝ) * (2 * Real.exp (L + 4 - L ^ 2) +
        Real.exp (-(X / 2)))) := h1.trans h2
    _ = (N : ℝ) * (Real.exp (2 * L + 10) * (2 * Real.exp (L + 4 - L ^ 2) +
        Real.exp (-(X / 2)))) := by ring
    _ ≤ (N : ℝ) * Real.exp (-L - 2) := mul_le_mul_of_nonneg_left h3 hN0.le


/-- **The mean square of `D₂` is tiny**: for `L ≥ 40`, `N = e^{L^{10}}`, `2 ≤ w ≤ 2 e^L` and
`R` with `e^{L^{10}/21}/2 ≤ R ≤ e^{L^{10}/21}`,
`N⁻¹ ∑_{n ≤ N} |∑_{q ∣ P(w), q > R} μ(q)/φ(q) c_q(n)|² ≤ e^{-L}`. -/
theorem avg_sq_tail_le {N w R : ℕ} {L : ℝ} (hL : 40 ≤ L) (hN : (N : ℝ) = Real.exp (L ^ 10))
    (hw2 : 2 ≤ w) (hwL : (w : ℝ) ≤ 2 * Real.exp L) (hR0 : 0 < R)
    (hRhi : (R : ℝ) ≤ Real.exp (L ^ 10 / 21)) (hRlo : Real.exp (L ^ 10 / 21) ≤ 2 * R) :
    (N : ℝ)⁻¹ * ∑ n ∈ Icc (1 : ℤ) N,
        ‖blockWeight ((primorialBelow w).divisors.filter (fun q => R < q)) n‖ ^ 2 ≤
      Real.exp (-L) := by
  set S : ℝ := (primorialBelow w : ℝ) / (Nat.totient (primorialBelow w) : ℝ) with hSdef
  set M : ℝ := ∑ n ∈ Icc (1 : ℤ) N, cramerModel w n with hM
  have hS1 : 1 ≤ S := one_le_primorialBelow_div_totient w
  have hN0 : (0 : ℝ) < N := by rw [hN]; exact Real.exp_pos _
  have ht := tailSum_le hL hw2 hwL hR0 hRlo
  have ht0 : 0 ≤ tailSum w R := Finset.sum_nonneg fun q _ => by positivity
  have hbrun := sum_cramerModel_sub_le hL hN hw2 hwL
  rw [← hSdef, ← hM] at hbrun
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    linarith only [mul_le_mul he1 he1 (by norm_num) (Real.exp_pos 1).le]
  have hexpL : Real.exp (-L - 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hexpL' : Real.exp (-L) = Real.exp (-L - 2) * Real.exp 2 := by
    rw [← Real.exp_add]; ring_nf
  have hδ : |M - N| ≤ N * Real.exp (-L - 2) := by
    have := mul_le_mul_of_nonneg_right hS1 (abs_nonneg (M - N))
    linarith only [this, hbrun]
  have hhead : headSum w R + tailSum w R = S := headSum_add_tailSum w R
  have hhead0 : 0 ≤ headSum w R := Finset.sum_nonneg fun q _ => by positivity
  have hsum := sum_norm_sq_tail_le w R N
  rw [← hSdef, ← hM] at hsum
  have hX := ten_pow_six_mul_sq_le hL
  have h40 : 40 * L ≤ L ^ 2 := by nlinarith only [hL]
  have hR4 : (R : ℝ) ^ 4 ≤ N * Real.exp (-L - 2) := by
    calc (R : ℝ) ^ 4 ≤ (Real.exp (L ^ 10 / 21)) ^ 4 :=
          pow_le_pow_left₀ (Nat.cast_nonneg R) hRhi 4
      _ = Real.exp (4 * (L ^ 10 / 21)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (L ^ 10 + (-L - 2)) := by
          refine Real.exp_le_exp.2 ?_
          linarith only [hX, h40, hL]
      _ = N * Real.exp (-L - 2) := by rw [hN, Real.exp_add]
  have hMle : M ≤ N + |M - N| := by
    have := le_abs_self (M - N)
    linarith
  have hNM : (N : ℝ) - M ≤ |M - N| := by
    have := neg_le_abs (M - N)
    linarith
  have hA1 : tailSum w R * M ≤ tailSum w R * (N + |M - N|) :=
    mul_le_mul_of_nonneg_left hMle ht0
  have hA2 : (S - tailSum w R) * ((N : ℝ) - M) ≤ S * |M - N| := by
    have h1 : (S - tailSum w R) * ((N : ℝ) - M) ≤ (S - tailSum w R) * |M - N| :=
      mul_le_mul_of_nonneg_left hNM (by linarith)
    have h2 : (S - tailSum w R) * |M - N| ≤ S * |M - N| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    exact h1.trans h2
  have ht1 : tailSum w R ≤ 1 := ht.trans hexpL
  have hB : tailSum w R * |M - N| ≤ N * Real.exp (-L - 2) := by
    calc tailSum w R * |M - N| ≤ 1 * (N * Real.exp (-L - 2)) :=
          mul_le_mul ht1 hδ (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hC : tailSum w R * N ≤ N * Real.exp (-L - 2) := by
    calc tailSum w R * N ≤ Real.exp (-L - 2) * N := mul_le_mul_of_nonneg_right ht hN0.le
      _ = _ := by ring
  have htotal : ∑ n ∈ Icc (1 : ℤ) N,
        ‖blockWeight ((primorialBelow w).divisors.filter (fun q => R < q)) n‖ ^ 2 ≤
      N * Real.exp (-L) := by
    refine hsum.trans ?_
    rw [hexpL']
    have hSδ : S * |M - N| ≤ N * Real.exp (-L - 2) := hbrun
    have hpos : 0 < N * Real.exp (-L - 2) := by positivity
    linarith only [hsum, hA1, hA2, hB, hC, hR4, hSδ, mul_le_mul_of_nonneg_left hexp2 hpos.le]
  rw [inv_mul_le_iff₀ hN0]
  exact htotal

end PrimeCarleson.Proof.Fplus31
