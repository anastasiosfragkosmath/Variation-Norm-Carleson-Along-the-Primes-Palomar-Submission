module

public import PrimeCarleson.Proof.Fplus31.ZeroFree.Cases

/-!
# The zero-free region for the Riemann zeta function

Part of the classical zero-free region (`ZeroFree/Main.lean`). For `ζ`, with `L₁ = (s-1) ζ(s)`
entire:

* `|γ| ≤ 1`: `ζ` has no zero near the segment `re s ≥ 1`, `|im s| ≤ 1` (compactness,
  `exists_zeta_zero_free_nbhd`);
* `|γ| > 1`: the `3-4-1` inequality at `σ = 1 + 10 b` with the pole terms `Re 1/(c - 1)` bounded by
  `1`, and the Landau lemma for `L₁` at `σ + iγ` (subtracting the zero) and `σ + 2iγ`.
-/

@[expose] public noncomputable section

open Complex Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.ZeroFree

open PNTSW

/-- **The zero-free region of `ζ`.** -/
theorem no_zero_zeta : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ s : ℂ, s ≠ 1 → riemannZeta s = 0 →
    ¬ (1 - c₀ / Real.log (|s.im| + 3) ≤ s.re) := by
  obtain ⟨C₀, hC₀, hzeta⟩ := neg_re_logDeriv_zeta_le
  obtain ⟨c₁, hc₁, hnbhd⟩ := exists_zeta_zero_free_nbhd
  obtain ⟨b₀, hb₀, hsmall⟩ := exists_small (K := 5000 + 3 * C₀ + 15000) (ε := 7 / 110)
    (by positivity) (by norm_num)
  refine ⟨min (min b₀ c₁) (1 / 70), lt_min (lt_min hb₀ hc₁) (by norm_num), ?_⟩
  intro s hs1 hs hreg
  have hH1 : 1 < Real.log (|s.im| + 3) := by
    have := log_mul_abs_add_three_gt_one (q := 1) le_rfl s.im
    simpa using this
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = Real.log (|s.im| + 3) := ⟨_, rfl⟩
  rw [← hH] at hH1 hreg
  have hH0 : 0 < H := by linarith
  have hc0 : 0 < min (min b₀ c₁) (1 / 70) := lt_min (lt_min hb₀ hc₁) (by norm_num)
  have hcb : min (min b₀ c₁) (1 / 70) ≤ b₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hcc : min (min b₀ c₁) (1 / 70) ≤ c₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hc70 : min (min b₀ c₁) (1 / 70) ≤ 1 / 70 := min_le_right _ _
  have hs_lt : s.re < 1 := by
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hs
  obtain ⟨hb0, hbH, hbc⟩ := region_setup hc0 hH1 hreg hs_lt
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 - s.re := ⟨_, rfl⟩
  rw [← hb] at hb0 hbH hbc
  by_cases hγ : |s.im| ≤ 1
  · exact hnbhd s hγ (by linarith) hs1 hs
  · push Not at hγ
    have hbH₀ : b ≤ b₀ / H := hbH.trans (div_le_div_of_nonneg_right hcb hH0.le)
    have hb70 : b ≤ 1 / 70 := hbc.trans hc70
    have hsm := hsmall H b hH1.le hb0 hbH₀
    have hδ0 : 0 < 10 * b := by linarith
    have hδ1 : 10 * b ≤ 1 := by linarith
    have hzL1 : zetaL1 s = 0 := by rw [zetaL1_apply hs1, hs, mul_zero]
    have hS1 : ∀ ρ ∈ ({s} : Finset ℂ),
        ‖ρ - (((1 + 10 * b : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)‖ < 1 / 2 ∧ zetaL1 ρ = 0 := by
      intro ρ hρ
      rw [Finset.mem_singleton] at hρ
      subst hρ
      exact ⟨norm_sub_center_lt hb hb0 hδ0 (by linarith), hzL1⟩
    have key1 := neg_re_logDeriv_zetaL1_le hδ0 hδ1 {s} hS1
    have key3 := neg_re_logDeriv_zetaL1_le (δ := 10 * b) (t := 2 * s.im) hδ0 hδ1 ∅ (by simp)
    have key0 := hzeta (10 * b) hδ0 hδ1
    have h341 := character_log_derivative_positivity (1 : DirichletCharacter ℂ 1) (1 + 10 * b)
      s.im (by linarith)
    simp only [DirichletCharacter.LFunction_modOne_eq] at h341
    have hre₁ : 1 < (((1 + 10 * b : ℝ) : ℂ) + (s.im : ℂ) * Complex.I).re := by
      simp
      linarith
    have hre₂ : 1 < (((1 + 10 * b : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I).re := by
      simp
      linarith
    have hZ1 := neg_re_logDeriv_zeta_eq hre₁
    have hZ2 := neg_re_logDeriv_zeta_eq hre₂
    have hγ2 : 1 ≤ s.im ^ 2 := by
      rw [← sq_abs]
      exact one_le_pow₀ hγ.le
    have hpole1 : (1 / ((((1 + 10 * b : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) - 1)).re ≤ 1 := by
      rw [re_one_div_sub_one]
      exact pole_le_one hδ0 hδ1 hγ2
    have hpole2 : (1 / ((((1 + 10 * b : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I) - 1)).re
        ≤ 1 := by
      rw [re_one_div_sub_one]
      exact pole_le_one hδ0 hδ1 (by rw [mul_pow]; linarith only [hγ2])
    have hdiv := re_one_div_center_sub (δ := 10 * b) (s := s) hb
    simp only [Finset.sum_singleton, Finset.card_singleton, Finset.sum_empty, Finset.card_empty,
      Nat.cast_one, Nat.cast_zero, neg_zero, zero_add, mul_zero, add_zero] at key1 key3
    rw [hdiv] at key1
    have hlog1 : Real.log (|s.im| + 4) ≤ H + 1 := by
      have h1 : |s.im| + 4 ≤ 2 * (|s.im| + 3) := by linarith [abs_nonneg s.im]
      calc Real.log (|s.im| + 4) ≤ Real.log (2 * (|s.im| + 3)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log 2 + H := by rw [Real.log_mul (by norm_num) (by positivity), hH]
        _ ≤ H + 1 := by
            have := Real.log_two_lt_d9
            linarith
    have hlog2 : Real.log (|2 * s.im| + 4) ≤ H + 1 := by
      have h1 : |2 * s.im| + 4 ≤ 2 * (|s.im| + 3) := by
        rw [abs_mul]
        simp only [abs_two]
        linarith [abs_nonneg s.im]
      calc Real.log (|2 * s.im| + 4) ≤ Real.log (2 * (|s.im| + 3)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log 2 + H := by rw [Real.log_mul (by norm_num) (by positivity), hH]
        _ ≤ H + 1 := by
            have := Real.log_two_lt_d9
            linarith
    have hlogδ : Real.log (3 / (10 * b)) ≤ Real.log (1 / b) :=
      log_three_div_le (by norm_num) hb0
    have hL0 : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by
      rw [le_div_iff₀ hb0]; linarith)
    have e1 : 1 / (10 * b + b) = (1 / 11) * (1 / b) := by field_simp; ring
    have e2 : 1 / (10 * b) = (1 / 10) * (1 / b) := by field_simp
    have e3 : (7 / 110) / b = (7 / 110) * (1 / b) := by field_simp
    have hK : 4640 * H + 2400 * Real.log (1 / b) + 14153 + 3 * C₀ ≤
        (5000 + 3 * C₀ + 15000) * (H + Real.log (1 / b) + 1) :=
      K_dom hC₀ hH0.le hL0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    rw [e3] at hsm
    rw [e2] at key0
    rw [e1] at key1
    linarith only [h341, key0, hZ1, hZ2, key1, key3, hpole1, hpole2, hlog1, hlog2, hlogδ, hK, hsm]

end PrimeCarleson.Proof.Fplus31.ZeroFree
