module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Nonprincipal
public import PrimeCarleson.Proof.Fplus31.PNTSW.LogDerivZeta

/-!
# The Riesz mean of `Λ` from the classical zero-free region

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The analogue of `PNTSW.Nonprincipal` for `ζ`: with `L₁(s) = (s-1) ζ(s)` entire
and zero-free for `re s ≥ 1 - c / log (|im s| + 3)`, the pole of `ζ` at `s = 1` is evaluated exactly
(`PNTSW.PoleKernel.riesz_zeta_split`: no residue theorem), and for `y ≥ y₀`

`|∑_{n ≤ y} Λ(n)(y-n) - (y-1)²/2| ≤ y² exp (-c₁ √(log y))` (`riesz_zeta_sw`).
-/

@[expose] public noncomputable section

open Complex ArithmeticFunction Filter
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- **The Riesz mean of `Λ`, with free parameters**: the bound `2B y^{(1-a/2)+1} + B
y^{(1+a/4)+1}/T`, `B = 1800 H²/c²`, `H = log (T + 4)`, `a = c/H`. -/
theorem riesz_L1_param {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hz : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → zetaL1 s ≠ 0)
    {T H a y : ℝ} (hT : 1 ≤ T) (hH : H = Real.log (T + 4)) (ha : a = c / H)
    (hy : 1 ≤ y) :
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * ((y : ℂ) - n) - (((y - 1) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      2 * (1800 * H ^ 2 / c ^ 2) * y ^ ((1 - a / 2) + 1) +
        (1800 * H ^ 2 / c ^ 2) * y ^ ((1 + a / 4) + 1) / T := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have hH1 : 1 < H := by
    have := one_lt_log_mul_add_four (q := 1) le_rfl (T := T) (by linarith)
    rw [hH]; simpa using this
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by linarith)]; nlinarith
  have hσ₁ : 1 < 1 + a / 4 := by linarith
  set B : ℝ := 1800 * H ^ 2 / c ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hform := riesz_zeta_split hσ₁ hy
  have hrect := perron_rect_bound (F := zetaL1) differentiable_zetaL1 (y := y)
    (σ₀ := 1 - a / 2) (σ₁ := 1 + a / 4) (T := T) (B₁ := B) (B₂ := B) hy (by linarith)
    (by linarith) hσ₁ hT ?_ ?_ ?_ ?_
  · rw [← hform, norm_mul] at hrect
    have h2π : ‖(((2 * π : ℝ)) : ℂ)‖ = 2 * π := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2π] at hrect
    set Y₀ : ℝ := y ^ ((1 - a / 2) + 1) with hY₀
    set Y₁ : ℝ := y ^ ((1 + a / 4) + 1) with hY₁
    have hY₁0 : 0 ≤ Y₁ := Real.rpow_nonneg hy0.le _
    have hT0 : 0 < T := by linarith
    have hs1 : (1 + a / 4 - (1 - a / 2)) ≤ 1 := by linarith
    have hT2 : 1 / T ^ 2 ≤ 1 / T := by
      apply one_div_le_one_div_of_le hT0
      exact le_self_pow₀ hT two_ne_zero
    have hmid : 2 * ((1 + a / 4 - (1 - a / 2)) * B * Y₁ / T ^ 2) ≤ 2 * (B * Y₁ / T) := by
      have : (1 + a / 4 - (1 - a / 2)) * B * Y₁ / T ^ 2 ≤ B * Y₁ / T := by
        calc (1 + a / 4 - (1 - a / 2)) * B * Y₁ / T ^ 2
            ≤ 1 * B * Y₁ / T ^ 2 := by
              gcongr
          _ = B * Y₁ * (1 / T ^ 2) := by ring
          _ ≤ B * Y₁ * (1 / T) := mul_le_mul_of_nonneg_left hT2 (by positivity)
          _ = B * Y₁ / T := by ring
      exact mul_le_mul_of_nonneg_left this zero_le_two
    have hpi : (3 : ℝ) < π := Real.pi_gt_three
    have h1 : 2 * π * ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * ((y : ℂ) - n) -
        (((y - 1) ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 2 * π * (2 * B * Y₀ + B * Y₁ / T) := by
      refine hrect.trans ?_
      have h3 : 0 ≤ B * Y₁ / T := by positivity
      have hp2 : (0 : ℝ) ≤ π - 2 := sub_nonneg.mpr ((by norm_num : (2 : ℝ) ≤ 3).trans hpi.le)
      linarith only [hmid, mul_nonneg h3 hp2]
    exact le_of_mul_le_mul_left h1 (by positivity)
  · intro s hs1 hs2 hs3
    refine hz s ?_
    have hlog : Real.log (|s.im| + 3) ≤ H := by
      rw [hH]
      exact Real.log_le_log (by positivity) (by linarith)
    have hlogpos : 0 < Real.log (|s.im| + 3) := by
      have := log_mul_abs_add_three_gt_one (q := 1) le_rfl s.im
      simpa using (by linarith : (0 : ℝ) < Real.log (((1 : ℕ) : ℝ) * (|s.im| + 3)))
    have : a ≤ c / Real.log (|s.im| + 3) := by
      rw [ha]; exact div_le_div_of_nonneg_left hc.le hlogpos hlog
    linarith
  · intro t
    have hre : ((((1 + a / 4 : ℝ) : ℂ)) + t * I).re = 1 + a / 4 := by simp
    have hs1 : (((1 + a / 4 : ℝ) : ℂ) + t * I) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hre] at this
      simp at this
      linarith
    rw [zetaL1_apply hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1)
      (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; linarith))
  · exact logDeriv_zetaL1_rect hc hc2 hz hT hH ha
  · intro t _
    have hre : ((((1 + a / 4 : ℝ) : ℂ)) + t * I).re = 1 + a / 4 := by simp
    have h := logDeriv_zetaL1_line (s := (((1 + a / 4 : ℝ) : ℂ)) + t * I)
      (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [hre] at h
    refine h.trans ?_
    have hc0 : c ≠ 0 := hc.ne'
    have hH0 : H ≠ 0 := by linarith
    have h14 : 1 + a / 4 - 1 = a / 4 := by ring
    have e : 8 / (1 + a / 4 - 1) ^ 2 + 1 / (1 + a / 4 - 1) = 128 * H ^ 2 / c ^ 2 + 4 * H / c := by
      rw [h14, ha]; field_simp; ring
    rw [e, hB]
    have h5 : 4 * H / c ≤ 4 * H ^ 2 / c ^ 2 := by
      rw [div_le_div_iff₀ hc (by positivity)]
      have hcH : c ≤ H := (hc2.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hH1.le
      calc 4 * H * c ^ 2 = (4 * H * c) * c := by ring
        _ ≤ (4 * H * c) * H := mul_le_mul_of_nonneg_left hcH (by positivity)
        _ = 4 * H ^ 2 * c := by ring
    have : 128 * H ^ 2 / c ^ 2 + 4 * H ^ 2 / c ^ 2 ≤ 1800 * H ^ 2 / c ^ 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (calc 128 * H ^ 2 + 4 * H ^ 2 = (128 + 4) * H ^ 2 := by ring
        _ ≤ 1800 * H ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg H)) (by positivity)
    linarith

/-- **The Riesz mean of `Λ`**, for `y ≥ y₀`:
`|∑_{n ≤ y} Λ(n)(y-n) - (y-1)²/2| ≤ y² exp (-c₁ √(log y))`. -/
theorem riesz_zeta_sw (hZ : ClassicalZeroFreeRegion) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ y₀ : ℝ, 1 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y →
      |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (y - n) - (y - 1) ^ 2 / 2| ≤
        y ^ 2 * Real.exp (-(c₁ * √(Real.log y))) := by
  obtain ⟨c, hc, hc2, hzero⟩ := zeroFree_zetaL1 hZ
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp
    (Fplus31.eventually_poly_le_exp 2 (3 * (1800 * 16) / c ^ 2) (c / 16) (by positivity))
  set u₁ : ℝ := max u₀ 2 with hu₁
  have hu₁2 : 2 ≤ u₁ := le_max_right _ _
  refine ⟨c / 16, by positivity, Real.exp (u₁ ^ 2), Real.one_le_exp (by positivity), ?_⟩
  intro y hy
  have hy1 : 1 ≤ y := le_trans (Real.one_le_exp (by positivity)) hy
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hlogy : u₁ ^ 2 ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos _) hy
    rwa [Real.log_exp] at this
  set u : ℝ := √(Real.log y) with hu
  have hlog : Real.log y = u ^ 2 := by
    rw [hu, Real.sq_sqrt (Real.log_nonneg hy1)]
  have hu1 : u₁ ≤ u := by
    rw [hu]
    exact Real.le_sqrt_of_sq_le hlogy
  have hu2 : 2 ≤ u := le_trans hu₁2 hu1
  have hu0u : u₀ ≤ u := le_trans (le_max_left _ _) hu1
  have hT1 : 1 ≤ Real.exp u := Real.one_le_exp (zero_le_two.trans hu2)
  have hH1 := le_log_mul_add_four (q := 1) le_rfl u
  have hH2 := log_mul_add_four_le (q := 1) le_rfl hu2 (by simp; linarith)
  simp only [Nat.cast_one, one_mul] at hH1 hH2
  set H : ℝ := Real.log (Real.exp u + 4) with hH
  have hparam := riesz_L1_param hc hc2 hzero (T := Real.exp u) (H := H) (a := c / H)
    hT1 hH rfl hy1
  have hB0 : 0 ≤ 1800 * H ^ 2 / c ^ 2 := by positivity
  have hB : 1800 * H ^ 2 / c ^ 2 ≤ (1800 * 16) * u ^ 2 / c ^ 2 := by
    have hHsq : H ^ 2 ≤ (4 * u) ^ 2 := pow_le_pow_left₀ ((zero_le_two.trans hu2).trans hH1) hH2 2
    exact div_le_div_of_nonneg_right
      (calc 1800 * H ^ 2 ≤ 1800 * (4 * u) ^ 2 := mul_le_mul_of_nonneg_left hHsq (by norm_num)
        _ = 1800 * 16 * u ^ 2 := by ring) (by positivity)
  have hbud := budget_bound (c := c) (u := u) (H := H) (a := c / H) (y := y)
    (B := 1800 * H ^ 2 / c ^ 2) (K := 1800 * 16) hc hc2 hy1 hu2 hlog hH1 hH2 rfl hB0 hB
  have hcast : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * ((y : ℂ) - n) - (((y - 1) ^ 2 / 2 : ℝ) : ℂ)
      = ((∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n * (y - n) - (y - 1) ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hparam
  refine hparam.trans (hbud.trans ?_)
  have hpoly := hu₀ u hu0u
  have hfac : 3 * ((1800 * 16) * u ^ 2 / c ^ 2) ≤ Real.exp (c / 16 * u) := by
    refine le_trans (le_of_eq ?_) hpoly
    ring
  calc 3 * ((1800 * 16) * u ^ 2 / c ^ 2) * y ^ 2 * Real.exp (-(c * u / 8))
      = (3 * ((1800 * 16) * u ^ 2 / c ^ 2) * Real.exp (-(c * u / 8))) * y ^ 2 := by ring
    _ ≤ (Real.exp (c / 16 * u) * Real.exp (-(c * u / 8))) * y ^ 2 := by
        gcongr
    _ = y ^ 2 * Real.exp (-(c / 16 * u)) := by
        rw [← Real.exp_add]; ring_nf

end PrimeCarleson.Proof.Fplus31.PNTSW
