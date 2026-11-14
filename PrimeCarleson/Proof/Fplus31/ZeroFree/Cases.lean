module

public import PrimeCarleson.Proof.Fplus31.ZeroFree.LBounds
public import PrimeCarleson.Proof.Fplus31.ZeroFree.Positivity

/-!
# The zero-free region: the non-real and the real characters

Part of the classical zero-free region (`ZeroFree/Main.lean`). Let `ρ = β + iγ` be a zero of
`L(s, χ)`, `b = 1 - β > 0`, `H = log (q (|γ| + 3))`, and suppose `b ≤ c₀ / H`.

* `exists_small`: the elementary estimate `K (H + log (1/b) + 1) < ε / b` for `b ≤ b₀ / H`;
* `no_zero_nonreal`: for `χ² ≠ 1` the `3-4-1` inequality at `σ = 1 + 10 b` contradicts a zero;
* `no_zero_real`: for `χ² = 1`, `χ ≠ 1` and `γ ≠ 0`, the `3-4-1` inequality (if `|γ| ≥ 10 b`) or the
  `1 + χ` inequality at `σ = 1 + 20 b` (if `|γ| < 10 b`, using the zeros `ρ`, `ρ̄`) contradicts a
  zero.
-/

@[expose] public noncomputable section

open Complex Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.ZeroFree

open PNTSW

/-- **The elementary estimate**: for `K, ε > 0` there is `b₀ > 0` with
`K (H + log (1/b) + 1) < ε / b` whenever `H ≥ 1` and `0 < b ≤ b₀ / H`. -/
theorem exists_small {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ H b : ℝ, 1 ≤ H → 0 < b → b ≤ b₀ / H →
      K * (H + Real.log (1 / b) + 1) < ε / b := by
  refine ⟨min (ε / (3 * K)) (ε ^ 2 / (9 * K ^ 2)), lt_min (by positivity) (by positivity), ?_⟩
  intro H b hH hb hbH
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℝ, b₀ = min (ε / (3 * K)) (ε ^ 2 / (9 * K ^ 2)) := ⟨_, rfl⟩
  rw [← hb₀] at hbH
  have hb₁ : b₀ ≤ ε / (3 * K) := hb₀ ▸ min_le_left _ _
  have hb₂ : b₀ ≤ ε ^ 2 / (9 * K ^ 2) := hb₀ ▸ min_le_right _ _
  have hH0 : 0 < H := by linarith
  have hbH' : b * H ≤ b₀ := by rwa [le_div_iff₀ hH0] at hbH
  obtain ⟨y, hy0, hy2⟩ : ∃ y : ℝ, 0 < y ∧ y ^ 2 = 1 / b :=
    ⟨Real.sqrt (1 / b), Real.sqrt_pos.2 (by positivity), Real.sq_sqrt (by positivity)⟩
  have hHy : H ≤ b₀ * y ^ 2 := by
    rw [hy2]
    have : H ≤ b₀ / b := by rw [le_div_iff₀ hb]; linarith
    calc H ≤ b₀ / b := this
      _ = b₀ * (1 / b) := by ring
  have hb₀pos : 0 < b₀ := by
    by_contra h
    push Not at h
    have : b * H ≤ 0 := by linarith only [hbH', h]
    exact absurd this (not_le.2 (mul_pos hb hH0))
  have hy_ge : 3 * K / ε ≤ y := by
    have h3 : b₀ * (9 * K ^ 2) ≤ ε ^ 2 := by rwa [le_div_iff₀ (by positivity)] at hb₂
    by_contra h
    push Not at h
    have h4 : y * ε < 3 * K := by rwa [lt_div_iff₀ hε] at h
    have h5 : (y * ε) ^ 2 < (3 * K) ^ 2 := by
      apply pow_lt_pow_left₀ h4 (by positivity) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hHy (sq_nonneg ε)]
  have hlog : Real.log (1 / b) ≤ 2 * (y - 1) := by
    rw [← hy2, Real.log_pow]
    push_cast
    have := Real.log_le_sub_one_of_pos hy0
    linarith
  have hKb : K * b₀ ≤ ε / 3 := by
    calc K * b₀ ≤ K * (ε / (3 * K)) := mul_le_mul_of_nonneg_left hb₁ hK.le
      _ = ε / 3 := by field_simp
  have hKy : K ≤ ε * y / 3 := by
    rw [div_le_iff₀ hε] at hy_ge
    linarith
  have key : ε / b = ε * y ^ 2 := by rw [hy2]; ring
  rw [key]
  have e1 : K * H ≤ K * (b₀ * y ^ 2) := mul_le_mul_of_nonneg_left hHy hK.le
  have e2 : K * b₀ * y ^ 2 ≤ ε / 3 * y ^ 2 := mul_le_mul_of_nonneg_right hKb (sq_nonneg y)
  have e3 : K * Real.log (1 / b) ≤ K * (2 * (y - 1)) := mul_le_mul_of_nonneg_left hlog hK.le
  have e4 : K * y ≤ ε * y / 3 * y := mul_le_mul_of_nonneg_right hKy hy0.le
  linarith only [e1, e2, e3, e4, hK]

/-- Real part of `1 / (c - ρ)`. -/
theorem re_one_div_sub (c ρ : ℂ) :
    (1 / (c - ρ)).re = (c.re - ρ.re) / ((c.re - ρ.re) ^ 2 + (c.im - ρ.im) ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  congr 1
  ring

/-- The disc condition: `‖ρ - c‖ ≤ |ρ.re - c.re| + |ρ.im - c.im|`. -/
theorem norm_sub_le_abs (c ρ : ℂ) : ‖ρ - c‖ ≤ |ρ.re - c.re| + |ρ.im - c.im| := by
  have := Complex.norm_le_abs_re_add_abs_im (ρ - c)
  simpa using this

/-- `log (q (|2γ| + 3)) ≤ log (q (|γ| + 3)) + 1`. -/
theorem log_two_mul_le {q : ℕ} (hq : 1 ≤ q) (γ : ℝ) :
    Real.log (q * (|2 * γ| + 3)) ≤ Real.log (q * (|γ| + 3)) + 1 := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) * (|2 * γ| + 3) ≤ 2 * (q * (|γ| + 3)) := by
    rw [abs_mul]
    simp only [abs_two]
    nlinarith [abs_nonneg γ]
  calc Real.log (q * (|2 * γ| + 3)) ≤ Real.log (2 * (q * (|γ| + 3))) :=
        Real.log_le_log (by positivity) h1
    _ = Real.log 2 + Real.log (q * (|γ| + 3)) :=
        Real.log_mul (by norm_num) (by positivity)
    _ ≤ Real.log (q * (|γ| + 3)) + 1 := by
        have := Real.log_two_lt_d9
        linarith

/-- Real part of `1 / (c - 1)` for `c = 1 + δ + it`. -/
theorem re_one_div_sub_one {δ t : ℝ} :
    (1 / ((((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)).re = δ / (δ ^ 2 + t ^ 2) := by
  rw [re_one_div_sub]
  have h1 : ((((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).re - (1 : ℂ).re) = δ := by simp
  have h2 : ((((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).im - (1 : ℂ).im) = t := by simp
  rw [h1, h2]

/-- `(-ζ'/ζ)(x) = (-L₁'/L₁)(x) + 1/(x-1)` for `re x > 1`, in real-part form. -/
theorem neg_re_logDeriv_zeta_eq {x : ℂ} (hx : 1 < x.re) :
    (-deriv riemannZeta x / riemannZeta x).re =
      (-deriv zetaL1 x / zetaL1 x).re + (1 / (x - 1)).re := by
  have hx1 : x ≠ 1 := by
    intro h
    rw [h] at hx
    simp at hx
  have hz : riemannZeta x ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hx
  have h := neg_logDeriv_zeta_split hx1 hz
  rw [neg_div, neg_div, h, Complex.add_re]

/-- The principal character: `-Re L'/L(χ₀) ≤ -Re ζ'/ζ + log q` on `re s > 1`. -/
theorem neg_re_logDeriv_principal_le {q : ℕ} [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s).re ≤
      (-deriv riemannZeta s / riemannZeta s).re + Real.log q := by
  have h := principal_neg_real_log_derivative_le q hs
  simpa [logDeriv_apply, neg_div] using h

/-- The set-up shared by the three cases: `b = 1 - β` is positive and at most `c₀ / H`. -/
theorem region_setup {c₀ H β : ℝ} (hc₀ : 0 < c₀) (hH : 1 < H) (hreg : 1 - c₀ / H ≤ β)
    (hβ : β < 1) : 0 < 1 - β ∧ 1 - β ≤ c₀ / H ∧ 1 - β ≤ c₀ := by
  have h1 : c₀ / H ≤ c₀ := div_le_self hc₀.le hH.le
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The centre minus the zero, for `c = 1 + δ + i Im s`. -/
theorem center_sub (δ : ℝ) (s : ℂ) :
    (((1 + δ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) - s = ((1 + δ - s.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp

/-- A zero at distance `δ + b` from the centre lies in the disc of radius `1/2`. -/
theorem norm_sub_center_lt {δ b : ℝ} {s : ℂ} (hb : b = 1 - s.re) (hb0 : 0 < b)
    (hδ : 0 < δ) (hsmall : δ + b < 1 / 2) :
    ‖s - (((1 + δ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)‖ < 1 / 2 := by
  rw [norm_sub_rev, center_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]
  linarith

/-- The real part of `1 / (c - s)` for `c = 1 + δ + i Im s`. -/
theorem re_one_div_center_sub {δ b : ℝ} {s : ℂ} (hb : b = 1 - s.re) :
    (1 / ((((1 + δ : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) - s)).re = 1 / (δ + b) := by
  rw [center_sub, one_div, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  congr 2
  rw [hb]
  ring

/-- Domination of the explicit error terms by the constant `K` of `exists_small`. -/
theorem K_dom {C₀ H L a b c p r m : ℝ} (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hL : 0 ≤ L) (hm : 0 ≤ m)
    (hr : 0 ≤ r) (hp : 0 ≤ p) (ha : a ≤ p) (hb : b ≤ p) (hc : c ≤ r) :
    a * H + b * L + c + m * C₀ ≤ (p + m * C₀ + r) * (H + L + 1) := by
  have h1 : a * H ≤ p * H := mul_le_mul_of_nonneg_right ha hH
  have h2 : b * L ≤ p * L := mul_le_mul_of_nonneg_right hb hL
  have h3 : 0 ≤ m * C₀ * (H + L) := by positivity
  have h4 : 0 ≤ r * (H + L) := by positivity
  linarith [h1, h2, h3, h4, hp, hc]

/-- `log (3 / (κ b)) ≤ log (1 / b)` for `κ ≥ 3`. -/
theorem log_three_div_le {κ b : ℝ} (hκ : 3 ≤ κ) (hb : 0 < b) :
    Real.log (3 / (κ * b)) ≤ Real.log (1 / b) := by
  refine Real.log_le_log (by positivity) ?_
  rw [div_le_div_iff₀ (by positivity) hb]
  nlinarith

/-- The pole term of `1/(c-1)` at height `t` with `4 δ² ≤ t²`. -/
theorem pole_le {δ t : ℝ} (hδ : 0 < δ) (h : 4 * δ ^ 2 ≤ t ^ 2) :
    δ / (δ ^ 2 + t ^ 2) ≤ 1 / (5 * δ) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The pole term of `1/(c-1)` at height `t` with `t² ≥ 1`, `δ ≤ 1`. -/
theorem pole_le_one {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : 1 ≤ t ^ 2) :
    δ / (δ ^ 2 + t ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith

/-- **No zero of a non-real character in the classical region.** -/
theorem no_zero_nonreal : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ^ 2 ≠ 1 → ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 →
      ¬ (1 - c₀ / Real.log (q * (|s.im| + 3)) ≤ s.re) := by
  obtain ⟨C₀, hC₀, hzeta⟩ := neg_re_logDeriv_zeta_le
  obtain ⟨b₀, hb₀, hsmall⟩ := exists_small (K := 2400 + 3 * C₀ + 9000) (ε := 7 / 110)
    (by positivity) (by norm_num)
  refine ⟨min b₀ (1 / 70), lt_min hb₀ (by norm_num), ?_⟩
  intro q _ χ hχ2 s hs hreg
  have hχ : χ ≠ 1 := fun h => hχ2 (by rw [h, one_pow])
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hH1 := log_mul_abs_add_three_gt_one hq1 s.im
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = Real.log (q * (|s.im| + 3)) := ⟨_, rfl⟩
  rw [← hH] at hH1 hreg
  have hH0 : 0 < H := by linarith
  have hc₁ : min b₀ (1 / 70) ≤ b₀ := min_le_left _ _
  have hc₂ : min b₀ (1 / 70) ≤ 1 / 70 := min_le_right _ _
  have hc0 : 0 < min b₀ (1 / 70) := lt_min hb₀ (by norm_num)
  have hs_lt : s.re < 1 := by
    by_contra h
    push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hs
  obtain ⟨hb0, hbH, hbc⟩ := region_setup hc0 hH1 hreg hs_lt
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 - s.re := ⟨_, rfl⟩
  rw [← hb] at hb0 hbH hbc
  have hbH₀ : b ≤ b₀ / H := hbH.trans (div_le_div_of_nonneg_right hc₁ hH0.le)
  have hb70 : b ≤ 1 / 70 := hbc.trans hc₂
  have hsm := hsmall H b hH1.le hb0 hbH₀
  have hδ0 : 0 < 10 * b := by linarith
  have hδ1 : 10 * b ≤ 1 := by linarith
  have hS1 : ∀ ρ ∈ ({s} : Finset ℂ),
      ‖ρ - (((1 + 10 * b : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)‖ < 1 / 2 ∧
        DirichletCharacter.LFunction χ ρ = 0 := by
    intro ρ hρ
    rw [Finset.mem_singleton] at hρ
    subst hρ
    exact ⟨norm_sub_center_lt hb hb0 hδ0 (by linarith), hs⟩
  have key1 := neg_re_logDeriv_L_le hχ hδ0 hδ1 {s} hS1
  have key3 := neg_re_logDeriv_L_le (χ := χ ^ 2) hχ2 (t := 2 * s.im) hδ0 hδ1 ∅ (by simp)
  have key0 := hzeta (10 * b) hδ0 hδ1
  have h341 := character_log_derivative_positivity χ (1 + 10 * b) s.im (by linarith)
  have hdiv := re_one_div_center_sub (δ := 10 * b) (s := s) hb
  simp only [Finset.sum_singleton, Finset.card_singleton, Finset.sum_empty, Finset.card_empty,
    Nat.cast_one, Nat.cast_zero, neg_zero, zero_add, mul_zero, add_zero] at key1 key3
  rw [hdiv] at key1
  have hlog3 := log_two_mul_le hq1 s.im
  rw [← hH] at hlog3 key1
  have hlogδ : Real.log (3 / (10 * b)) ≤ Real.log (1 / b) :=
    log_three_div_le (by norm_num) hb0
  have hL0 : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by
    rw [le_div_iff₀ hb0]; linarith)
  have e1 : 1 / (10 * b + b) = (1 / 11) * (1 / b) := by field_simp; ring
  have e2 : 1 / (10 * b) = (1 / 10) * (1 / b) := by field_simp
  have e3 : (7 / 110) / b = (7 / 110) * (1 / b) := by field_simp
  have hK : 2320 * H + 1200 * Real.log (1 / b) + 7592 + 3 * C₀ ≤
      (2400 + 3 * C₀ + 9000) * (H + Real.log (1 / b) + 1) :=
    K_dom hC₀ hH0.le hL0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  rw [e3] at hsm
  rw [e2] at key0
  rw [e1] at key1
  linarith

/-- The `|γ| ≥ 10 b` half of the real case. -/
theorem no_zero_real_far : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → χ ^ 2 = 1 → ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 →
      10 * (1 - s.re) ≤ |s.im| → ¬ (1 - c₀ / Real.log (q * (|s.im| + 3)) ≤ s.re) := by
  obtain ⟨C₀, hC₀, hzeta⟩ := neg_re_logDeriv_zeta_le
  obtain ⟨b₀, hb₀, hsmall⟩ := exists_small (K := 3000 + 3 * C₀ + 9000) (ε := 12 / 275)
    (by positivity) (by norm_num)
  refine ⟨min b₀ (1 / 70), lt_min hb₀ (by norm_num), ?_⟩
  intro q _ χ hχ hχ2 s hs hfar hreg
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hH1 := log_mul_abs_add_three_gt_one hq1 s.im
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = Real.log (q * (|s.im| + 3)) := ⟨_, rfl⟩
  rw [← hH] at hH1 hreg
  have hH0 : 0 < H := by linarith
  have hc₁ : min b₀ (1 / 70) ≤ b₀ := min_le_left _ _
  have hc₂ : min b₀ (1 / 70) ≤ 1 / 70 := min_le_right _ _
  have hc0 : 0 < min b₀ (1 / 70) := lt_min hb₀ (by norm_num)
  have hs_lt : s.re < 1 := by
    by_contra h
    push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hs
  obtain ⟨hb0, hbH, hbc⟩ := region_setup hc0 hH1 hreg hs_lt
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 - s.re := ⟨_, rfl⟩
  rw [← hb] at hb0 hbH hbc hfar
  have hbH₀ : b ≤ b₀ / H := hbH.trans (div_le_div_of_nonneg_right hc₁ hH0.le)
  have hb70 : b ≤ 1 / 70 := hbc.trans hc₂
  have hsm := hsmall H b hH1.le hb0 hbH₀
  have hδ0 : 0 < 10 * b := by linarith
  have hδ1 : 10 * b ≤ 1 := by linarith
  have hS1 : ∀ ρ ∈ ({s} : Finset ℂ),
      ‖ρ - (((1 + 10 * b : ℝ) : ℂ) + (s.im : ℂ) * Complex.I)‖ < 1 / 2 ∧
        DirichletCharacter.LFunction χ ρ = 0 := by
    intro ρ hρ
    rw [Finset.mem_singleton] at hρ
    subst hρ
    exact ⟨norm_sub_center_lt hb hb0 hδ0 (by linarith), hs⟩
  have key1 := neg_re_logDeriv_L_le hχ hδ0 hδ1 {s} hS1
  have key3 := neg_re_logDeriv_zetaL1_le (δ := 10 * b) (t := 2 * s.im) hδ0 hδ1 ∅ (by simp)
  have key0 := hzeta (10 * b) hδ0 hδ1
  have h341 := character_log_derivative_positivity χ (1 + 10 * b) s.im (by linarith)
  rw [hχ2] at h341
  have hre₂ : 1 < (((1 + 10 * b : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I).re := by
    simp
    linarith
  have hP := neg_re_logDeriv_principal_le (q := q) hre₂
  have hZ := neg_re_logDeriv_zeta_eq hre₂
  have hpole := re_one_div_sub_one (δ := 10 * b) (t := 2 * s.im)
  have hpole_le : (10 * b) / ((10 * b) ^ 2 + (2 * s.im) ^ 2) ≤ 1 / (5 * (10 * b)) := by
    refine pole_le (by positivity) ?_
    have : (10 * b) ^ 2 ≤ s.im ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg s.im] : -|s.im| ≤ 10 * b) hfar
      rwa [sq_abs] at this
    linarith only [this]
  have hdiv := re_one_div_center_sub (δ := 10 * b) (s := s) hb
  simp only [Finset.sum_singleton, Finset.card_singleton, Finset.sum_empty, Finset.card_empty,
    Nat.cast_one, Nat.cast_zero, neg_zero, zero_add, mul_zero, add_zero] at key1 key3
  rw [hdiv] at key1
  have hlogq : Real.log q ≤ H := by
    rw [hH]
    exact Real.log_le_log (by positivity)
      (le_mul_of_one_le_right (by positivity) (by linarith only [abs_nonneg s.im]))
  have hlog4 : Real.log (|2 * s.im| + 4) ≤ H + 1 := by
    have h1 : |2 * s.im| + 4 ≤ 2 * (q * (|s.im| + 3)) := by
      rw [abs_mul]
      simp only [abs_two]
      linarith only [mul_nonneg (sub_nonneg.2 hq1') (abs_nonneg s.im), hq1']
    calc Real.log (|2 * s.im| + 4) ≤ Real.log (2 * (q * (|s.im| + 3))) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log 2 + H := by rw [Real.log_mul (by norm_num) (by positivity), hH]
      _ ≤ H + 1 := by
          have := Real.log_two_lt_d9
          linarith
  rw [← hH] at key1
  have hlogδ : Real.log (3 / (10 * b)) ≤ Real.log (1 / b) :=
    log_three_div_le (by norm_num) hb0
  have hL0 : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by
    rw [le_div_iff₀ hb0]; linarith)
  have e1 : 1 / (10 * b + b) = (1 / 11) * (1 / b) := by field_simp; ring
  have e2 : 1 / (10 * b) = (1 / 10) * (1 / b) := by field_simp
  have e4 : 1 / (5 * (10 * b)) = (1 / 50) * (1 / b) := by field_simp; ring
  have e3 : (12 / 275) / b = (12 / 275) * (1 / b) := by field_simp
  have hK : 2785 * H + 1440 * Real.log (1 / b) + 8532 + 3 * C₀ ≤
      (3000 + 3 * C₀ + 9000) * (H + Real.log (1 / b) + 1) :=
    K_dom hC₀ hH0.le hL0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  rw [e3] at hsm
  rw [e2] at key0
  rw [e1] at key1
  rw [e4] at hpole_le
  linarith

/-- The `|γ| < 10 b` half of the real case. -/
theorem no_zero_real_near : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → χ ^ 2 = 1 → ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 →
      s.im ≠ 0 → |s.im| < 10 * (1 - s.re) →
        ¬ (1 - c₀ / Real.log (q * (|s.im| + 3)) ≤ s.re) := by
  obtain ⟨C₀, hC₀, hzeta⟩ := neg_re_logDeriv_zeta_le
  obtain ⟨b₀, hb₀, hsmall⟩ := exists_small (K := 500 + C₀ + 1500) (ε := 299 / 10820)
    (by positivity) (by norm_num)
  refine ⟨min b₀ (1 / 70), lt_min hb₀ (by norm_num), ?_⟩
  intro q _ χ hχ hχ2 s hs hγ hnear hreg
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hH1 := log_mul_abs_add_three_gt_one hq1 s.im
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = Real.log (q * (|s.im| + 3)) := ⟨_, rfl⟩
  rw [← hH] at hH1 hreg
  have hH0 : 0 < H := by linarith
  have hc₁ : min b₀ (1 / 70) ≤ b₀ := min_le_left _ _
  have hc₂ : min b₀ (1 / 70) ≤ 1 / 70 := min_le_right _ _
  have hc0 : 0 < min b₀ (1 / 70) := lt_min hb₀ (by norm_num)
  have hs_lt : s.re < 1 := by
    by_contra h
    push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hs
  obtain ⟨hb0, hbH, hbc⟩ := region_setup hc0 hH1 hreg hs_lt
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 - s.re := ⟨_, rfl⟩
  rw [← hb] at hb0 hbH hbc hnear
  have hbH₀ : b ≤ b₀ / H := hbH.trans (div_le_div_of_nonneg_right hc₁ hH0.le)
  have hb70 : b ≤ 1 / 70 := hbc.trans hc₂
  have hsm := hsmall H b hH1.le hb0 hbH₀
  have hδ0 : 0 < 20 * b := by linarith
  have hδ1 : 20 * b ≤ 1 := by linarith
  have hreal : ∀ a : ZMod q, (χ a).im = 0 := im_eq_zero_of_sq_eq_one hχ2
  have hne : s ≠ (starRingEnd ℂ) s := fun h => hγ (Complex.conj_eq_iff_im.1 h.symm)
  have hconj : DirichletCharacter.LFunction χ ((starRingEnd ℂ) s) = 0 := by
    rw [LFunction_conj_of_real hχ hreal, hs, map_zero]
  have hγ2 : s.im ^ 2 < 100 * b ^ 2 := by
    have h1 := abs_lt.1 hnear
    have := sq_lt_sq' h1.1 h1.2
    linarith only [this]
  have hS2 : ∀ ρ ∈ ({s, (starRingEnd ℂ) s} : Finset ℂ),
      ‖ρ - (((1 + 20 * b : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ < 1 / 2 ∧
        DirichletCharacter.LFunction χ ρ = 0 := by
    intro ρ hρ
    have hρ' : ρ = s ∨ ρ = (starRingEnd ℂ) s := by simpa using hρ
    have hbound : ∀ ρ : ℂ, ρ.re = s.re → |ρ.im| = |s.im| →
        ‖ρ - (((1 + 20 * b : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ < 1 / 2 := by
      intro ρ h1 h2
      have h3 := norm_sub_le_abs (((1 + 20 * b : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) ρ
      have e1 : (((1 + 20 * b : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I).re = 1 + 20 * b := by simp
      have e2 : (((1 + 20 * b : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I).im = 0 := by simp
      rw [e1, e2, h1, sub_zero, h2] at h3
      rw [abs_of_nonpos (by linarith : s.re - (1 + 20 * b) ≤ 0)] at h3
      linarith
    rcases hρ' with rfl | rfl
    · exact ⟨hbound ρ rfl rfl, hs⟩
    · exact ⟨hbound _ (by simp) (by simp), hconj⟩
  have key1 := neg_re_logDeriv_L_le hχ hδ0 hδ1 {s, (starRingEnd ℂ) s} hS2
  have hc0' : (((1 + 20 * b : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = ((1 + 20 * b : ℝ) : ℂ) := by
    simp
  rw [hc0', Finset.sum_pair hne, Finset.card_pair hne] at key1
  have key0 := hzeta (20 * b) hδ0 hδ1
  have h1p := real_character_log_derivative_positivity χ hreal (1 + 20 * b) (by linarith)
  have hterm : ∀ ρ : ℂ, ρ.re = s.re → ρ.im ^ 2 = s.im ^ 2 →
      21 / (541 * b) ≤ (1 / (((1 + 20 * b : ℝ) : ℂ) - ρ)).re := by
    intro ρ h1 h2
    rw [re_one_div_sub]
    have e1 : (((1 + 20 * b : ℝ) : ℂ)).re = 1 + 20 * b := by simp
    have e2 : (((1 + 20 * b : ℝ) : ℂ)).im = 0 := by simp
    rw [e1, e2, h1, zero_sub, neg_sq, h2]
    have e3 : 1 + 20 * b - s.re = 21 * b := by rw [hb]; ring
    rw [e3]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [hγ2]
  have hsum1 := hterm s rfl rfl
  have hsum2 := hterm ((starRingEnd ℂ) s) (by simp) (by simp)
  have hlogq : Real.log (q * (|(0 : ℝ)| + 3)) ≤ H := by
    rw [hH]
    exact Real.log_le_log (by positivity) (by
      rw [abs_zero, zero_add]
      exact mul_le_mul_of_nonneg_left (by linarith only [abs_nonneg s.im]) (by positivity))
  have hlogδ : Real.log (3 / (20 * b)) ≤ Real.log (1 / b) :=
    log_three_div_le (by norm_num) hb0
  have hL0 : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by
    rw [le_div_iff₀ hb0]; linarith)
  have e1 : 1 / (20 * b) = (1 / 20) * (1 / b) := by field_simp
  have e2 : 21 / (541 * b) = (21 / 541) * (1 / b) := by field_simp
  have e3 : (299 / 10820) / b = (299 / 10820) * (1 / b) := by field_simp
  have hK : 464 * H + 240 * Real.log (1 / b) + 1428 + C₀ ≤
      (500 + C₀ + 1500) * (H + Real.log (1 / b) + 1) := by
    have := K_dom (m := 1) hC₀ hH0.le hL0 (a := 464) (b := 240) (c := 1428) (p := 500) (r := 1500)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using this
  rw [e3] at hsm
  rw [e1] at key0
  rw [e2] at hsum1 hsum2
  simp only [Nat.cast_ofNat] at key1
  have t1 : 42 / 541 * (1 / b) ≤ (1 / (((1 + 20 * b : ℝ) : ℂ) - s)).re +
      (1 / (((1 + 20 * b : ℝ) : ℂ) - (starRingEnd ℂ) s)).re := by linarith [hsum1, hsum2]
  have t2 : 464 * Real.log (q * (|(0 : ℝ)| + 3)) ≤ 464 * H := by linarith [hlogq]
  have t3 : 240 * Real.log (3 / (20 * b)) ≤ 240 * Real.log (1 / b) := by linarith [hlogδ]
  have key1' : (-deriv (DirichletCharacter.LFunction χ) ((1 + 20 * b : ℝ) : ℂ) /
        DirichletCharacter.LFunction χ ((1 + 20 * b : ℝ) : ℂ)).re ≤
      -((1 / (((1 + 20 * b : ℝ) : ℂ) - s)).re +
        (1 / (((1 + 20 * b : ℝ) : ℂ) - (starRingEnd ℂ) s)).re) +
      (464 * Real.log (q * (|(0 : ℝ)| + 3)) + 240 * Real.log (3 / (20 * b)) + 1428) :=
    key1.trans (le_of_eq (by ring))
  have s1 : (-deriv (DirichletCharacter.LFunction χ) ((1 + 20 * b : ℝ) : ℂ) /
        DirichletCharacter.LFunction χ ((1 + 20 * b : ℝ) : ℂ)).re ≤
      -(42 / 541 * (1 / b)) + (464 * H + 240 * Real.log (1 / b) + 1428) := by
    refine key1'.trans (add_le_add (neg_le_neg t1) ?_)
    exact add_le_add_left (add_le_add t2 t3) 1428
  linarith only [h1p, key0, s1, hK, hsm]

/-- **No zero of a real character with `Im ρ ≠ 0` in the classical region.** -/
theorem no_zero_real : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → χ ^ 2 = 1 → ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → s.im ≠ 0 →
      ¬ (1 - c₀ / Real.log (q * (|s.im| + 3)) ≤ s.re) := by
  obtain ⟨c₁, hc₁, h₁⟩ := no_zero_real_far
  obtain ⟨c₂, hc₂, h₂⟩ := no_zero_real_near
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro q _ χ hχ hχ2 s hs hγ hreg
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hH1 := log_mul_abs_add_three_gt_one hq1 s.im
  have hmono : ∀ c : ℝ, min c₁ c₂ ≤ c →
      1 - c / Real.log (q * (|s.im| + 3)) ≤ s.re := fun c hc =>
    le_trans (by
      have : min c₁ c₂ / Real.log (q * (|s.im| + 3)) ≤ c / Real.log (q * (|s.im| + 3)) :=
        div_le_div_of_nonneg_right hc (by linarith)
      linarith) hreg
  rcases le_or_gt (10 * (1 - s.re)) |s.im| with hfar | hnear
  · exact h₁ q χ hχ hχ2 s hs hfar (hmono c₁ (min_le_left _ _))
  · exact h₂ q χ hχ hχ2 s hs hγ hnear (hmono c₂ (min_le_right _ _))

end PrimeCarleson.Proof.Fplus31.ZeroFree
