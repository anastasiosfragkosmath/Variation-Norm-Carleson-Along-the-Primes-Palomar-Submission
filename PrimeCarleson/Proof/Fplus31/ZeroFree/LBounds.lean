module

public import PrimeCarleson.Proof.Fplus31.ZeroFree.Blaschke
public import PrimeCarleson.Proof.Fplus31.PNTSW.Bounds
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.ReImTopology

/-!
# Growth, lower bounds and Landau instances for `L(s, χ)` and `L₁ = (s-1) ζ`

Part of the classical zero-free region (`ZeroFree/Main.lean`). On the line `re s = 1 + δ`:

* `inv_le_norm_LFunction`: `‖L(s, χ)‖ ≥ 1 / (σ/(σ-1) + 1)` (the Möbius inverse series);
* `neg_re_logDeriv_L_le`, `neg_re_logDeriv_zetaL1_le`: the Landau lemma at radius `1/2` for
  `L(·, χ)` (`χ ≠ 1`) and for `L₁`, subtracting any finite set `S` of zeros in the disc;
* `neg_re_logDeriv_zeta_le`: `-Re ζ'/ζ (1 + δ) ≤ 1/δ + C₀` for `0 < δ ≤ 1`;
* `LFunction_conj_of_real`: `L(s̄, χ) = conj L(s, χ)` for a real character;
* `exists_zeta_zero_free_nbhd`: `ζ` has no zero in a neighbourhood of the segment `re s ≥ 1`,
  `|im s| ≤ 1` (compactness);
* `three_le_of_ne_one`, `im_eq_zero_of_sq_eq_one`: elementary facts on characters.
-/

@[expose] public noncomputable section

open Complex Set Metric

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.ZeroFree

open PNTSW

/-- **Lower bound for `L`**: `1 / (σ/(σ-1) + 1) ≤ ‖L(s, χ)‖` for `σ = re s > 1`. -/
theorem inv_le_norm_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    1 / (s.re / (s.re - 1) + 1) ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have h1 := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hpos : 0 < s.re / (s.re - 1) + 1 := by
    have : 0 < s.re - 1 := by linarith
    positivity
  have h2 : ‖LSeries ((fun n : ℕ => χ n) *
      fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤
      1 * (s.re / (s.re - 1) + 1) := by
    refine norm_LSeries_le_zetaSum (K := 1) (ε := 0) (τ := s.re) zero_le_one hs (by linarith) ?_
    intro n _
    rw [Real.rpow_zero, mul_one, Pi.mul_apply, norm_mul]
    have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc ‖χ n‖ * ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul (χ.norm_le_one n) hμ (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  rw [div_le_iff₀ hpos]
  nlinarith [norm_nonneg (LSeries (fun n : ℕ => χ n) s)]

/-- `ζ` version of `inv_le_norm_LFunction`. -/
theorem inv_le_norm_zeta {s : ℂ} (hs : 1 < s.re) :
    1 / (s.re / (s.re - 1) + 1) ≤ ‖riemannZeta s‖ := by
  have := inv_le_norm_LFunction (1 : DirichletCharacter ℂ 1) hs
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

/-- The Landau lemma at radius `1/2`, in the form used below. -/
theorem landau_half {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℂ} {M A : ℝ} (hM : 0 < M)
    (hA : 0 ≤ A) (hb : ∀ z, ‖z - c‖ ≤ 1 / 2 → ‖F z‖ ≤ Real.exp M)
    (hlow : Real.exp (-A) ≤ ‖F c‖) (hzero : ∀ z, F z = 0 → z.re ≤ c.re) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ‖ρ - c‖ < 1 / 2 ∧ F ρ = 0) :
    ∑ ρ ∈ S, (1 / (c - ρ)).re ≤
      (deriv F c / F c).re + 464 * M + 240 * A + 960 + 2 * S.card := by
  have h := landau hF (r := 1 / 2) (by norm_num) hM hA hb hlow (fun z _ hz => hzero z hz) S hS
  have h1 : ∑ ρ ∈ S, (c - ρ).re / (1 / 2) ^ 2 ≤ ∑ _ρ ∈ S, (2 : ℝ) := by
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have h2 := (hS ρ hρ).1
    have h3 : (c - ρ).re ≤ ‖c - ρ‖ := Complex.re_le_norm _
    rw [norm_sub_rev] at h2
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  rw [Finset.sum_sub_distrib] at h
  simp only [Finset.sum_const, nsmul_eq_mul] at h1
  have e : (232 * M + 120 * A + 480) / (1 / 2) = 464 * M + 240 * A + 960 := by ring
  rw [e] at h
  linarith

/-- Bound for `L` on the ball of radius `1/2` around a point of `1 < re c ≤ 2`. -/
theorem norm_LFunction_le_ball {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {c z : ℂ} (hc1 : 1 < c.re) (hc2 : c.re ≤ 2) (hz : ‖z - c‖ ≤ 1 / 2) :
    ‖DirichletCharacter.LFunction χ z‖ ≤ 2 * q * (|c.im| + 3) := by
  have h1 := Complex.abs_re_le_norm (z - c)
  have hre : 1 / 2 < z.re := by
    have := (abs_le.1 (h1.trans hz)).1
    simp only [Complex.sub_re] at this
    linarith
  have hzn : ‖z‖ ≤ |c.im| + 3 := by
    have h2 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by simpa using norm_add_le c (z - c)
    have h3 : ‖c‖ ≤ |c.re| + |c.im| := Complex.norm_le_abs_re_add_abs_im c
    rw [abs_of_pos (by linarith : 0 < c.re)] at h3
    linarith
  have h := norm_LFunction_le hχ (s := z) (by linarith)
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hT : 0 ≤ |c.im| + 3 := by positivity
  have : (q : ℝ) * ‖z‖ ≤ q * (|c.im| + 3) := mul_le_mul_of_nonneg_left hzn hq
  nlinarith [mul_nonneg (mul_nonneg hq hT) (by linarith : (0 : ℝ) ≤ z.re - 1 / 2)]

/-- **Landau for `L(·, χ)`**: for `χ ≠ 1`, `c = 1 + δ + it`, and a finite set `S` of zeros of
`L(·, χ)` in the disc of radius `1/2` around `c`,
`-Re L'/L (c) ≤ -∑_{ρ ∈ S} Re 1/(c - ρ) + 464 log (q (|t|+3)) + 240 log (3/δ) + 1424 + 2 |S|`. -/
theorem neg_re_logDeriv_L_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ‖ρ - (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ < 1 / 2 ∧
      DirichletCharacter.LFunction χ ρ = 0) :
    (-deriv (DirichletCharacter.LFunction χ) (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      -∑ ρ ∈ S, (1 / ((((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ρ)).re +
        (464 * Real.log (q * (|t| + 3)) + 240 * Real.log (3 / δ) + 1424 + 2 * S.card) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I := ⟨_, rfl⟩
  rw [← hc] at hS ⊢
  have hcre : c.re = 1 + δ := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hX : 6 ≤ 2 * (q : ℝ) * (|t| + 3) := by nlinarith [abs_nonneg t]
  have hM : 0 < Real.log (2 * q * (|t| + 3)) := Real.log_pos (by linarith)
  have hA : 0 ≤ Real.log (3 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hb : ∀ z, ‖z - c‖ ≤ 1 / 2 →
      ‖DirichletCharacter.LFunction χ z‖ ≤ Real.exp (Real.log (2 * q * (|t| + 3))) := by
    intro z hz
    rw [Real.exp_log (by linarith)]
    have := norm_LFunction_le_ball hχ (c := c) (by rw [hcre]; linarith)
      (by rw [hcre]; linarith) hz
    rwa [hcim] at this
  have hlow : Real.exp (-Real.log (3 / δ)) ≤ ‖DirichletCharacter.LFunction χ c‖ := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    have h1 := inv_le_norm_LFunction χ (s := c) (by rw [hcre]; linarith)
    refine le_trans ?_ h1
    rw [hcre]
    have e : (1 + δ) / (1 + δ - 1) + 1 ≤ 3 / δ := by
      have h2 : 1 + δ - 1 = δ := by ring
      rw [h2, div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]
      linarith
    rw [one_div]
    exact inv_anti₀ (by
      have : 0 < (1 + δ) / (1 + δ - 1) := div_pos (by linarith) (by linarith)
      linarith) e
  have hzero : ∀ z, DirichletCharacter.LFunction χ z = 0 → z.re ≤ c.re := by
    intro z hz
    by_contra hlt
    push Not at hlt
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hcre] at hlt; linarith) hz
  have h := landau_half (DirichletCharacter.differentiable_LFunction hχ) hM hA hb hlow hzero S hS
  have e1 : (-deriv (DirichletCharacter.LFunction χ) c / DirichletCharacter.LFunction χ c).re =
      -(deriv (DirichletCharacter.LFunction χ) c / DirichletCharacter.LFunction χ c).re := by
    rw [neg_div, Complex.neg_re]
  rw [e1]
  have hlog2 : Real.log (2 * q * (|t| + 3)) ≤ Real.log (q * (|t| + 3)) + 1 := by
    rw [show 2 * (q : ℝ) * (|t| + 3) = 2 * (q * (|t| + 3)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_two_lt_d9
    linarith
  linarith

/-- Bound for `L₁` on the ball of radius `1/2` around a point of `1 < re c ≤ 2`. -/
theorem norm_zetaL1_le_ball {c z : ℂ} (hc1 : 1 < c.re) (hc2 : c.re ≤ 2) (hz : ‖z - c‖ ≤ 1 / 2) :
    ‖zetaL1 z‖ ≤ 3 * (|c.im| + 4) ^ 2 := by
  have h1 := Complex.abs_re_le_norm (z - c)
  have hre : 1 / 2 < z.re := by
    have := (abs_le.1 (h1.trans hz)).1
    simp only [Complex.sub_re] at this
    linarith
  have hzn : ‖z‖ ≤ |c.im| + 3 := by
    have h2 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by simpa using norm_add_le c (z - c)
    have h3 : ‖c‖ ≤ |c.re| + |c.im| := Complex.norm_le_abs_re_add_abs_im c
    rw [abs_of_pos (by linarith : 0 < c.re)] at h3
    linarith
  have hz1 : ‖z - 1‖ ≤ |c.im| + 4 := by
    have := norm_sub_le z 1
    simp only [norm_one] at this
    linarith
  have h := norm_zetaL1_le (s := z) (by linarith)
  have hT : 0 ≤ |c.im| := abs_nonneg _
  have h2 : ‖z‖ * ‖z - 1‖ / z.re ≤ (|c.im| + 3) * (|c.im| + 4) / (1 / 2) :=
    div_le_div₀ (by positivity) (mul_le_mul hzn hz1 (norm_nonneg _) (by positivity))
      (by norm_num) hre.le
  have h3 : ‖z‖ ≤ |c.im| + 3 := hzn
  nlinarith [h, h2, h3]

/-- A zero of `L₁` has real part `< 1`. -/
theorem zetaL1_zero_re_lt {z : ℂ} (hz : zetaL1 z = 0) : z.re < 1 := by
  by_contra h
  push Not at h
  by_cases h1 : z = 1
  · rw [h1] at hz
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1 hz
  · rw [zetaL1_apply h1] at hz
    rcases mul_eq_zero.1 hz with h2 | h2
    · exact h1 (sub_eq_zero.1 h2)
    · exact riemannZeta_ne_zero_of_one_le_re h h2

/-- **Landau for `L₁`**: for `c = 1 + δ + it` and a finite set `S` of zeros of `L₁` in the disc of
radius `1/2` around `c`,
`-Re L₁'/L₁ (c) ≤ -∑_{ρ ∈ S} Re 1/(c - ρ) + 928 log (|t|+4) + 480 log (3/δ) + 1900 + 2 |S|`. -/
theorem neg_re_logDeriv_zetaL1_le {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ‖ρ - (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ < 1 / 2 ∧ zetaL1 ρ = 0) :
    (-deriv zetaL1 (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        zetaL1 (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      -∑ ρ ∈ S, (1 / ((((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ρ)).re +
        (928 * Real.log (|t| + 4) + 480 * Real.log (3 / δ) + 1900 + 2 * S.card) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I := ⟨_, rfl⟩
  rw [← hc] at hS ⊢
  have hcre : c.re = 1 + δ := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have hX : 48 ≤ 3 * (|t| + 4) ^ 2 := by nlinarith [abs_nonneg t]
  have hM : 0 < Real.log (3 * (|t| + 4) ^ 2) := Real.log_pos (by linarith)
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hA : 0 ≤ Real.log (3 / δ ^ 2) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ2]; nlinarith)
  have hb : ∀ z, ‖z - c‖ ≤ 1 / 2 → ‖zetaL1 z‖ ≤ Real.exp (Real.log (3 * (|t| + 4) ^ 2)) := by
    intro z hz
    rw [Real.exp_log (by linarith)]
    have := norm_zetaL1_le_ball (c := c) (by rw [hcre]; linarith) (by rw [hcre]; linarith) hz
    rwa [hcim] at this
  have hlow : Real.exp (-Real.log (3 / δ ^ 2)) ≤ ‖zetaL1 c‖ := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    have hc1 : c ≠ 1 := by
      intro h
      rw [h] at hcre
      simp at hcre
      linarith
    have h1 := inv_le_norm_zeta (s := c) (by rw [hcre]; linarith)
    rw [zetaL1_apply hc1, norm_mul]
    have e : (1 + δ) / (1 + δ - 1) + 1 ≤ 3 / δ := by
      have h2 : 1 + δ - 1 = δ := by ring
      rw [h2, div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]
      linarith
    rw [hcre] at h1
    have h3 : δ / 3 ≤ ‖riemannZeta c‖ := by
      refine le_trans ?_ h1
      rw [one_div]
      calc δ / 3 = (3 / δ)⁻¹ := by field_simp
        _ ≤ _ := inv_anti₀ (by
          have : 0 < (1 + δ) / (1 + δ - 1) := div_pos (by linarith) (by linarith)
          linarith) e
    have h4 : δ ≤ ‖c - 1‖ := by
      have := Complex.re_le_norm (c - 1)
      simp only [Complex.sub_re, Complex.one_re, hcre] at this
      linarith
    calc (3 / δ ^ 2)⁻¹ = δ * (δ / 3) := by field_simp
      _ ≤ ‖c - 1‖ * ‖riemannZeta c‖ :=
        mul_le_mul h4 h3 (by positivity) (norm_nonneg _)
  have hzero : ∀ z, zetaL1 z = 0 → z.re ≤ c.re := by
    intro z hz
    have := zetaL1_zero_re_lt hz
    rw [hcre]
    linarith
  have h := landau_half differentiable_zetaL1 hM hA hb hlow hzero S hS
  have e1 : (-deriv zetaL1 c / zetaL1 c).re = -(deriv zetaL1 c / zetaL1 c).re := by
    rw [neg_div, Complex.neg_re]
  rw [e1]
  have hlog3 : Real.log (3 * (|t| + 4) ^ 2) ≤ 2 * Real.log (|t| + 4) + 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    push_cast
    linarith
  have hlog4 : Real.log (3 / δ ^ 2) ≤ 2 * Real.log (3 / δ) := by
    have h5 : 3 / δ ^ 2 ≤ (3 / δ) ^ 2 := by
      rw [div_pow, div_le_div_iff_of_pos_right hδ2]; nlinarith
    calc Real.log (3 / δ ^ 2) ≤ Real.log ((3 / δ) ^ 2) :=
          Real.log_le_log (by positivity) h5
      _ = 2 * Real.log (3 / δ) := by rw [Real.log_pow]; push_cast; ring
  linarith

/-- **`-Re ζ'/ζ (1 + δ) ≤ 1/δ + C₀`** for `0 < δ ≤ 1`. -/
theorem neg_re_logDeriv_zeta_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    (-deriv riemannZeta ((1 + δ : ℝ) : ℂ) / riemannZeta ((1 + δ : ℝ) : ℂ)).re ≤ 1 / δ + C := by
  have hcont : ContinuousOn (fun x : ℝ => -deriv zetaL1 (x : ℂ) / zetaL1 (x : ℂ))
      (Icc (1 : ℝ) 2) := by
    refine (DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1).comp
      Complex.continuous_ofReal.continuousOn ?_
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · left
      rw [← h]
      simp
    · right
      rw [LFunctionTrivChar_one_eq]
      exact riemannZeta_ne_zero_of_one_lt_re (by simpa using h)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun δ hδ hδ1 => ?_⟩
  have hx : (1 + δ) ∈ Icc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have h1 := hC (1 + δ) hx
  set s : ℂ := ((1 + δ : ℝ) : ℂ) with hs
  have hsre : s.re = 1 + δ := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsre
    simp at hsre
    linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; linarith)
  have hsplit := neg_logDeriv_zeta_split hs1 hz
  have e1 : (-deriv riemannZeta s / riemannZeta s) =
      -(deriv zetaL1 s / zetaL1 s) + 1 / (s - 1) := by rw [neg_div]; exact hsplit
  rw [e1, Complex.add_re]
  have e2 : (1 / (s - 1)).re = 1 / δ := by
    have : s - 1 = ((δ : ℝ) : ℂ) := by simp [hs]
    rw [this, one_div, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have e3 : (-(deriv zetaL1 s / zetaL1 s)).re ≤ max C 0 := by
    have h2 : (-(deriv zetaL1 s / zetaL1 s)).re ≤ ‖-(deriv zetaL1 s / zetaL1 s)‖ :=
      Complex.re_le_norm _
    have h3 : ‖-deriv zetaL1 s / zetaL1 s‖ ≤ C := h1
    rw [neg_div] at h3
    exact h2.trans (h3.trans (le_max_left _ _))
  linarith

/-- `L(s̄, χ) = conj L(s, χ)` for a nonprincipal real character. -/
theorem LFunction_conj_of_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (s : ℂ) :
    DirichletCharacter.LFunction χ (starRingEnd ℂ s) =
      starRingEnd ℂ (DirichletCharacter.LFunction χ s) := by
  have hd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hg_an : AnalyticOnNhd ℂ
      (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ => (differentiableAt_conj_conj_iff.mpr (hd _)).differentiableWithinAt)
      isOpen_univ
  have hgz : ∀ z : ℂ, 1 < z.re →
      starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)) =
        DirichletCharacter.LFunction χ z := by
    intro z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hz),
      DirichletCharacter.LFunction_eq_LSeries χ hz, LSeries, LSeries, Complex.conj_tsum]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
        Complex.conj_eq_iff_im.2 (hreal n), Complex.cpow_conj _ _
          (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.conj_conj,
        Complex.conj_natCast]
  have heq : EqOn (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)))
      (DirichletCharacter.LFunction χ) univ :=
    hg_an.eqOn_of_preconnected_of_eventuallyEq (hd.differentiableOn.analyticOnNhd isOpen_univ)
      isPreconnected_univ (mem_univ (2 : ℂ))
      (Filter.eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp)) hgz)
  have := heq (mem_univ (starRingEnd ℂ s))
  simp only [Complex.conj_conj] at this
  rw [← this]

/-- **`ζ` has no zero near the segment `re s ≥ 1`, `|im s| ≤ 1`.** -/
theorem exists_zeta_zero_free_nbhd : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ s : ℂ, |s.im| ≤ 1 → 1 - c₁ ≤ s.re →
    s ≠ 1 → riemannZeta s ≠ 0 := by
  set K : Set ℂ := (Icc (1 / 2 : ℝ) 2) ×ℂ (Icc (-1 : ℝ) 1) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  set Z : Set ℂ := K ∩ {s | zetaL1 s = 0} with hZ
  have hZc : IsCompact Z :=
    hKc.inter_right (isClosed_eq differentiable_zetaL1.continuous continuous_const)
  have hmem : ∀ s : ℂ, |s.im| ≤ 1 → 1 / 2 ≤ s.re → s.re < 1 → riemannZeta s = 0 → s ≠ 1 →
      s ∈ Z := by
    intro s him hre1 hre2 hz hs1
    refine ⟨?_, ?_⟩
    · rw [hK, Complex.mem_reProdIm]
      exact ⟨⟨hre1, by linarith⟩, abs_le.1 him⟩
    · change zetaL1 s = 0
      rw [zetaL1_apply hs1, hz, mul_zero]
  by_cases hne : Z.Nonempty
  · obtain ⟨s₀, hs₀, hmax⟩ := hZc.exists_isMaxOn hne Complex.continuous_re.continuousOn
    have hlt : s₀.re < 1 := zetaL1_zero_re_lt hs₀.2
    refine ⟨min (1 / 2) ((1 - s₀.re) / 2), lt_min (by norm_num) (by linarith), ?_⟩
    intro s him hre hs1 hzero
    have hc1 : min (1 / 2) ((1 - s₀.re) / 2) ≤ 1 / 2 := min_le_left _ _
    have hc2 : min (1 / 2) ((1 - s₀.re) / 2) ≤ (1 - s₀.re) / 2 := min_le_right _ _
    have hslt : s.re < 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_le_re h hzero
    have hsZ := hmem s him (by linarith) hslt hzero hs1
    have := hmax hsZ
    simp only [Set.mem_ofPred_eq] at this
    linarith
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro s him hre hs1 hzero
    have hslt : s.re < 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_le_re h hzero
    exact hne ⟨s, hmem s him (by linarith) hslt hzero hs1⟩

/-- A nonprincipal character has modulus at least `3`. -/
theorem three_le_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    3 ≤ q := by
  by_contra h
  apply hχ
  have hq : q = 1 ∨ q = 2 := by
    have := NeZero.pos q
    omega
  rcases hq with rfl | rfl
  · exact DirichletCharacter.level_one χ
  · refine MulChar.ext' fun a => ?_
    have ha : a = 0 ∨ a = 1 := by revert a; decide
    rcases ha with rfl | rfl
    · have h0 : ¬ IsUnit (0 : ZMod 2) := not_isUnit_zero
      rw [MulChar.map_nonunit χ h0, MulChar.map_nonunit (1 : DirichletCharacter ℂ 2) h0]
    · simp

/-- A character with `χ² = 1` takes real values. -/
theorem im_eq_zero_of_sq_eq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ^ 2 = 1)
    (a : ZMod q) : (χ a).im = 0 := by
  by_cases ha : IsUnit a
  · have h1 : χ a ^ 2 = 1 := by
      have := congrArg (fun ψ : DirichletCharacter ℂ q => ψ a) h
      simp only [MulChar.one_apply ha] at this
      rwa [χ.pow_apply' (by norm_num)] at this
    have h2 : (χ a - 1) * (χ a + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · rw [sub_eq_zero.1 h3]; simp
    · rw [eq_neg_of_add_eq_zero_left h3]; simp
  · rw [MulChar.map_nonunit χ ha]; simp

end PrimeCarleson.Proof.Fplus31.ZeroFree
