module

public import PrimeCarleson.Proof.Fplus31.C2.IterationChain

/-!
# The Cramér-model comparison, the Brun parameters of a stage

Part of the final parameters of the iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1).
For `N = e^U`, `U = u^{10}` with `u ≥ 3`, `w = cramerLevel N ≤ 2 e^u` and a level `P ≥ 0` with
`P² ≤ U`, the level `k + 1 = ⌈e² (log log w + 4) + P + 8⌉` makes the numeric `L¹` bound of the Brun
truncation (`cramer_brun_L1_Icc`) at most `3 U e^{-P} N / 8` and `w^{3 k} ≤ N²`; this is
`BrunOK N P`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `x^m = e^{m log x}` for `x > 0`. -/
theorem pow_eq_exp_mul {x : ℝ} (hx : 0 < x) (m : ℕ) : x ^ m = Real.exp (m * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

/-- **The first part of the Brun bound**: `e⁵ log w · N (e (ℓ + 4) / j)^j ≤ 3 U e^{-P} N / 16`
for `j ≥ e² (ℓ + 4) + P + 8`, `ℓ = log log w`. -/
theorem brun_T1 {N j : ℕ} {lw ℓ P U : ℝ} (hlwe : Real.exp ℓ = lw) (hjR : (0 : ℝ) < j)
    (hP0 : 0 ≤ P) (hℓ4 : 0 ≤ ℓ + 4) (hj_ge : Real.exp 2 * (ℓ + 4) + P + 8 ≤ j) (hU12 : 12 ≤ U) :
    Real.exp 5 * lw * ((N : ℝ) * (Real.exp 1 * (ℓ + 4) / j) ^ j) ≤
      3 * U * Real.exp (-P) * N / 16 := by
  have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hex : ℓ + 4 ≤ Real.exp 2 * (ℓ + 4) :=
    le_mul_of_one_le_left hℓ4 he2
  have hb0 : 0 ≤ Real.exp 1 * (ℓ + 4) / j := by positivity
  have hb1 : Real.exp 1 * (ℓ + 4) / j ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hjR]
    have h1 : Real.exp (-1) * Real.exp 2 = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    calc Real.exp 1 * (ℓ + 4) = Real.exp (-1) * (Real.exp 2 * (ℓ + 4)) := by
          rw [← mul_assoc, h1]
      _ ≤ Real.exp (-1) * j :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hb2 : (Real.exp 1 * (ℓ + 4) / j) ^ j ≤ Real.exp (-(j : ℝ)) := by
    calc (Real.exp 1 * (ℓ + 4) / j) ^ j ≤ Real.exp (-1) ^ j := pow_le_pow_left₀ hb0 hb1 j
      _ = Real.exp (-(j : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h1 : Real.exp (-(j : ℝ)) ≤ Real.exp (-(P + ℓ + 8)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp 5 * lw * Real.exp (-(P + ℓ + 8)) = Real.exp (-P) * Real.exp (-3) := by
    rw [← hlwe, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-3) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlw0 : 0 ≤ lw := by rw [← hlwe]; exact (Real.exp_pos _).le
  calc Real.exp 5 * lw * ((N : ℝ) * (Real.exp 1 * (ℓ + 4) / j) ^ j) ≤
      Real.exp 5 * lw * ((N : ℝ) * Real.exp (-(P + ℓ + 8))) := by
        gcongr
        exact hb2.trans h1
    _ = N * (Real.exp 5 * lw * Real.exp (-(P + ℓ + 8))) := by ring
    _ = N * (Real.exp (-P) * Real.exp (-3)) := by rw [h2]
    _ ≤ N * (Real.exp (-P) * 1) := by gcongr
    _ ≤ 3 * U * Real.exp (-P) * N / 16 := by
        have hX : 0 ≤ (N : ℝ) * Real.exp (-P) := by positivity
        have h16 : (16 : ℝ) * ((N : ℝ) * Real.exp (-P)) ≤ (3 * U) * ((N : ℝ) * Real.exp (-P)) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
        have : 3 * U * Real.exp (-P) * N / 16 = (3 * U) * ((N : ℝ) * Real.exp (-P)) / 16 := by
          ring
        rw [this]
        linarith

/-- **The second part of the Brun bound**: `e⁵ log w · w^j ≤ 3 U e^{-P} N / 16`, for
`w^{j-1} ≤ e^{2U/3}`, `w ≤ 2 e^u`, `log w ≤ 2 u`, `P ≤ u^5`, `U = u^{10}`, `u ≥ 3`. -/
theorem brun_T2 {N j w : ℕ} {lw P U u : ℝ} (hU : U = u ^ 10) (hu : 3 ≤ u) (hPu : P ≤ u ^ 5)
    (hN : (N : ℝ) = Real.exp U) (hw : (w : ℝ) ≤ 2 * Real.exp u) (hwpos : (0 : ℝ) < w)
    (hlw_hi : lw ≤ 2 * u) (hj1 : 1 ≤ j)
    (hwk : (w : ℝ) ^ (j - 1) ≤ Real.exp (2 * U / 3)) :
    Real.exp 5 * lw * (w : ℝ) ^ j ≤ 3 * U * Real.exp (-P) * N / 16 := by
  have hu0 : 0 ≤ u := by linarith
  have hu4 : (81 : ℝ) ≤ u ^ 4 := by
    calc (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hu5 : 81 * u ≤ u ^ 5 := by
    calc 81 * u ≤ u ^ 4 * u := mul_le_mul_of_nonneg_right hu4 hu0
      _ = u ^ 5 := by ring
  have hu5' : (243 : ℝ) ≤ u ^ 5 := by linarith
  have hwj : (w : ℝ) ^ j ≤ Real.exp (2 * U / 3) * (2 * Real.exp u) := by
    have : (w : ℝ) ^ j = (w : ℝ) ^ (j - 1) * w := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    exact mul_le_mul hwk hw hwpos.le (Real.exp_pos _).le
  have h1 : Real.exp 5 * lw * (w : ℝ) ^ j ≤
      Real.exp 5 * (2 * u) * (Real.exp (2 * U / 3) * (2 * Real.exp u)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlw_hi (Real.exp_pos _).le) hwj (by positivity)
      (by positivity)
  have h2 : Real.exp 5 * (2 * u) * (Real.exp (2 * U / 3) * (2 * Real.exp u)) =
      4 * Real.exp 5 * u * Real.exp (2 * U / 3 + u) := by
    rw [Real.exp_add]; ring
  have haa : 243 * u ^ 5 ≤ u ^ 5 * u ^ 5 := mul_le_mul_of_nonneg_right hu5' (by positivity)
  have hua : u ≤ u ^ 5 := by linarith
  have hUe : U = u ^ 5 * u ^ 5 := by rw [hU]; ring
  have h3 : 20 ≤ U / 3 - u - P := by linarith
  have h4 : (4 : ℝ) * Real.exp 5 ≤ Real.exp (U / 3 - u - P) := by
    have h6 : (2 : ℝ) ^ 15 ≤ Real.exp 15 := by
      have := two_pow_le_exp 15
      simpa using this
    have h7 : Real.exp 20 ≤ Real.exp (U / 3 - u - P) := Real.exp_le_exp.mpr h3
    have h4' : (4 : ℝ) * Real.exp 5 ≤ (2 : ℝ) ^ 15 * Real.exp 5 :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos 5).le
    have h6' : (2 : ℝ) ^ 15 * Real.exp 5 ≤ Real.exp 15 * Real.exp 5 :=
      mul_le_mul_of_nonneg_right h6 (Real.exp_pos 5).le
    have h20 : Real.exp 15 * Real.exp 5 = Real.exp 20 := by rw [← Real.exp_add]; norm_num
    linarith
  have h8 : (3 * U / 16) * Real.exp (U - P) = 3 * U * Real.exp (-P) * N / 16 := by
    rw [hN, show U - P = U + -P by ring, Real.exp_add]; ring
  have h9 : Real.exp (U - P) = Real.exp (2 * U / 3 + u) * Real.exp (U / 3 - u - P) := by
    rw [← Real.exp_add]; congr 1; ring
  have hu9 : (19683 : ℝ) ≤ u ^ 9 := by
    calc (19683 : ℝ) = 3 ^ 9 := by norm_num
      _ ≤ u ^ 9 := pow_le_pow_left₀ (by norm_num) hu 9
  have h10 : u ≤ 3 * U / 16 := by
    have h' : u * 19683 ≤ u * u ^ 9 := mul_le_mul_of_nonneg_left hu9 hu0
    have h'' : U = u * u ^ 9 := by rw [hU]; ring
    linarith
  have h11 : 4 * Real.exp 5 * u ≤ (3 * U / 16) * Real.exp (U / 3 - u - P) := by
    calc 4 * Real.exp 5 * u = (4 * Real.exp 5) * u := by ring
      _ ≤ Real.exp (U / 3 - u - P) * (3 * U / 16) := mul_le_mul h4 h10 hu0 (Real.exp_pos _).le
      _ = (3 * U / 16) * Real.exp (U / 3 - u - P) := mul_comm _ _
  have h12 := mul_le_mul_of_nonneg_right h11 (Real.exp_pos (2 * U / 3 + u)).le
  rw [← h8, h9]
  calc Real.exp 5 * lw * (w : ℝ) ^ j ≤ 4 * Real.exp 5 * u * Real.exp (2 * U / 3 + u) :=
        h1.trans (le_of_eq h2)
    _ ≤ (3 * U / 16) * Real.exp (U / 3 - u - P) * Real.exp (2 * U / 3 + u) := h12
    _ = (3 * U / 16) * (Real.exp (2 * U / 3 + u) * Real.exp (U / 3 - u - P)) := by ring

/-- **The Brun parameters.**  See the module docstring. -/
theorem brun_params {N w : ℕ} {u P U : ℝ} (hU : U = u ^ 10) (hu : 3 ≤ u) (hP0 : 0 ≤ P)
    (hP : P ^ 2 ≤ U) (hN : (N : ℝ) = Real.exp U) (hw2 : 2 ≤ w)
    (hw : (w : ℝ) ≤ 2 * Real.exp u) :
    ∃ k : ℕ, w ≤ N ∧ (w ^ k) ^ 3 ≤ N ^ 2 ∧
      Real.exp 5 * Real.log w * ((N : ℝ) * (Real.exp 1 * (Real.log (Real.log w) + 4) /
          ((k + 1 : ℕ) : ℝ)) ^ (k + 1) + (w : ℝ) ^ (k + 1)) ≤ 3 * U * Real.exp (-P) * N / 8 := by
  have hw2R : (2 : ℝ) ≤ w := by exact_mod_cast hw2
  have hwpos : (0 : ℝ) < w := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hu4 : (81 : ℝ) ≤ u ^ 4 := by
    calc (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hu5 : 81 * u ≤ u ^ 5 := by
    calc 81 * u ≤ u ^ 4 * u := mul_le_mul_of_nonneg_right hu4 hu0
      _ = u ^ 5 := by ring
  have hu5' : (243 : ℝ) ≤ u ^ 5 := by linarith only [hu5, hu]
  have hu10 : 81 * u ^ 6 ≤ u ^ 10 := by
    calc 81 * u ^ 6 ≤ u ^ 4 * u ^ 6 := mul_le_mul_of_nonneg_right hu4 (by positivity)
      _ = u ^ 10 := by ring
  have hU12 : (12 : ℝ) ≤ U := by
    rw [hU]; exact le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 10)
  have hPu5 : P ≤ u ^ 5 := by
    by_contra h
    push Not at h
    have h1 : (u ^ 5) ^ 2 < P ^ 2 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have h2 : (u ^ 5) ^ 2 = U := by rw [hU]; ring
    linarith
  set lw := Real.log w with hlw
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hlw_lo : (1 : ℝ) / 2 ≤ lw := by
    have : Real.log 2 ≤ lw := Real.log_le_log (by norm_num) hw2R
    linarith
  have hlw_hi : lw ≤ 2 * u := by
    have h1 : lw ≤ Real.log (2 * Real.exp u) := Real.log_le_log hwpos hw
    rw [Real.log_mul (by norm_num) (Real.exp_pos u).ne', Real.log_exp] at h1
    linarith
  have hlw0 : 0 < lw := by linarith
  set ℓ := Real.log lw with hℓ
  have hℓ_lo : -1 ≤ ℓ := by
    have h1 : Real.log (1 / 2) ≤ Real.log lw := Real.log_le_log (by norm_num) hlw_lo
    rw [one_div, Real.log_inv] at h1
    linarith
  have hℓ_hi : ℓ ≤ u := by
    have h2u : 2 * u ≤ Real.exp u := by
      have := Real.quadratic_le_exp_of_nonneg hu0
      linarith only [this, sq_nonneg (u - 1)]
    have h1 : ℓ ≤ Real.log (Real.exp u) := Real.log_le_log hlw0 (by linarith)
    rwa [Real.log_exp] at h1
  have he1 := Real.exp_one_lt_d9
  have he2 : Real.exp 2 ≤ 7.4 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    calc Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
          mul_le_mul he1.le he1.le (Real.exp_pos 1).le (by norm_num)
      _ ≤ 7.4 := by norm_num
  have he2' : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hℓ4 : 0 ≤ ℓ + 4 := by linarith
  have hE0 : 0 ≤ Real.exp 2 * (ℓ + 4) := mul_nonneg (Real.exp_pos 2).le hℓ4
  -- the level
  set j : ℕ := ⌈Real.exp 2 * (ℓ + 4) + P + 8⌉₊ with hj
  have hj_ge : Real.exp 2 * (ℓ + 4) + P + 8 ≤ j := Nat.le_ceil _
  have hj_lt : (j : ℝ) < Real.exp 2 * (ℓ + 4) + P + 8 + 1 :=
    Nat.ceil_lt_add_one (by linarith only [hE0, hP0])
  have hj_le : (j : ℝ) ≤ 20 * u ^ 5 := by
    have : Real.exp 2 * (ℓ + 4) ≤ 7.4 * (u + 4) := mul_le_mul he2 (by linarith) hℓ4 (by norm_num)
    linarith
  have hj1 : 1 ≤ j := by
    have : (1 : ℝ) ≤ j := by linarith only [hj_ge, hE0, hP0]
    exact_mod_cast this
  have hjR : (0 : ℝ) < j := Nat.cast_pos.mpr hj1
  have hk : (((j - 1 : ℕ)) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j 1
  have hk3 : (3 * ((j - 1 : ℕ) : ℝ)) * lw ≤ 2 * U := by
    have h3 : ((j - 1 : ℕ) : ℝ) * lw ≤ 20 * u ^ 5 * (2 * u) :=
      mul_le_mul (hk.trans hj_le) hlw_hi hlw0.le (by positivity)
    rw [hU]
    linarith only [h3, hu10, pow_nonneg hu0 10]
  have hwk : (w : ℝ) ^ (j - 1) ≤ Real.exp (2 * U / 3) := by
    have h1 : ((w : ℝ) ^ (j - 1)) ^ 3 ≤ (Real.exp (2 * U / 3)) ^ 3 := by
      rw [← pow_mul, pow_eq_exp_mul hwpos, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      push_cast
      linarith only [hk3]
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.exp_pos _).le h1
  refine ⟨j - 1, ?_, ?_, ?_⟩
  · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h1 : (w : ℝ) ≤ Real.exp (u + 1) :=
      calc (w : ℝ) ≤ 2 * Real.exp u := hw
        _ ≤ Real.exp 1 * Real.exp u := mul_le_mul_of_nonneg_right he (Real.exp_pos u).le
        _ = Real.exp (u + 1) := by rw [Real.exp_add, mul_comm]
    have hu6 : u ≤ u ^ 6 := le_self_pow₀ (by linarith) (by norm_num)
    have h2 : (w : ℝ) ≤ N := by
      rw [hN]
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      rw [hU]
      linarith only [hu, hu6, hu10]
    exact_mod_cast h2
  · have h2 : (((w ^ (j - 1)) ^ 3 : ℕ) : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [← pow_mul, pow_eq_exp_mul hwpos, hN, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      push_cast
      linarith only [hk3]
    exact_mod_cast h2
  · have hjk : ((j - 1 + 1 : ℕ)) = j := by omega
    rw [hjk]
    have hlwe : Real.exp ℓ = lw := Real.exp_log hlw0
    have hT1 := brun_T1 (N := N) (j := j) hlwe hjR hP0 hℓ4 hj_ge hU12
    have hT2 := brun_T2 (N := N) (j := j) (w := w) hU hu hPu5 hN hw hwpos hlw_hi hj1 hwk
    have hfin : Real.exp 5 * lw * ((N : ℝ) * (Real.exp 1 * (ℓ + 4) / j) ^ j + (w : ℝ) ^ j) =
        Real.exp 5 * lw * ((N : ℝ) * (Real.exp 1 * (ℓ + 4) / j) ^ j) +
          Real.exp 5 * lw * (w : ℝ) ^ j := by ring
    change Real.exp 5 * lw * ((N : ℝ) * (Real.exp 1 * (ℓ + 4) / ((j : ℕ) : ℝ)) ^ j +
      (w : ℝ) ^ j) ≤ _
    rw [hfin]
    linarith

end PrimeCarleson.Proof.Fplus31
