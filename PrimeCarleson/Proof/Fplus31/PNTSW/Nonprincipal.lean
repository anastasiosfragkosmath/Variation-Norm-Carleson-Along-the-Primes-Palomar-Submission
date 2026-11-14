module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Rect
public import PrimeCarleson.Proof.Fplus31.PNTSW.LogDeriv
public import PrimeCarleson.Proof.Fplus31.PNTSW.ZeroFree
public import PrimeCarleson.Proof.Fplus31.PNTSW.Budget
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Riesz mean of a nonprincipal character from the classical zero-free region

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). For a nonprincipal character `χ` modulo `q` whose `L`-function has no zero with
`re s ≥ 1 - c / log (q (|im s| + 3))`:

* `riesz_L_param`: for every height `T ≥ 1` and `y ≥ 1`,
  `‖∑_{n ≤ y} χ(n)Λ(n)(y-n)‖ ≤ 2B y^{(1-a/2)+1} + B y^{(1+a/4)+1}/T` with `H = log (q (T+4))`,
  `a = c/H`, `B = 666 H²/c²`: the exact Perron formula on `re s = 1 + a/4`
  (`PNTSW.Perron`), the truncation at height `T` and the contour shift to `re s = 1 - a/2`
  (`PNTSW.Rect`), the Landau bound on `L'/L` (`PNTSW.LogDeriv`);
* `riesz_nonprincipal_sw`: with `T = exp √(log y)`, uniformly for `log q ≤ √(log y)`,
  `‖∑_{n ≤ y} χ(n)Λ(n)(y-n)‖ ≤ y² exp (-c₁ √(log y))` for `y ≥ y₀`, `c₁` absolute.
-/

@[expose] public noncomputable section

open Complex ArithmeticFunction Filter
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- **The Riesz mean of a nonprincipal character, with free parameters**: the bound `2B
y^{(1-a/2)+1} + B y^{(1+a/4)+1}/T`, `B = 666 H²/c²`, `H = log (q (T + 4))`, `a = c/H`. -/
theorem riesz_L_param {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hz : ∀ s : ℂ, 1 - c / Real.log (q * (|s.im| + 3)) ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0)
    {T H a y : ℝ} (hT : 1 ≤ T) (hH : H = Real.log (q * (T + 4))) (ha : a = c / H)
    (hy : 1 ≤ y) :
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, χ n * (Λ n : ℂ) * ((y : ℂ) - n)‖ ≤
      2 * (666 * H ^ 2 / c ^ 2) * y ^ ((1 - a / 2) + 1) +
        (666 * H ^ 2 / c ^ 2) * y ^ ((1 + a / 4) + 1) / T := by
  have hy0 : 0 < y := by linarith
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hH1 : 1 < H := by rw [hH]; exact one_lt_log_mul_add_four hq1 (by linarith)
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by linarith)]; linarith
  have hσ₁ : 1 < 1 + a / 4 := by linarith
  set B : ℝ := 666 * H ^ 2 / c ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hform := riesz_formula χ hσ₁ hy0
  have hrect := perron_rect_bound (F := DirichletCharacter.LFunction χ)
    (DirichletCharacter.differentiable_LFunction hχ) (y := y) (σ₀ := 1 - a / 2)
    (σ₁ := 1 + a / 4) (T := T) (B₁ := B) (B₂ := B) hy (by linarith) (by linarith) hσ₁ hT
    ?_ ?_ ?_ ?_
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
      linarith
    have hpi : (3 : ℝ) < π := Real.pi_gt_three
    have h1 : 2 * π * ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, χ n * (Λ n : ℂ) * ((y : ℂ) - n)‖ ≤
        2 * π * (2 * B * Y₀ + B * Y₁ / T) := by
      refine hrect.trans ?_
      have h3 : 0 ≤ B * Y₁ / T := by positivity
      linarith [mul_nonneg h3 (by linarith : (0 : ℝ) ≤ π - 2)]
    exact le_of_mul_le_mul_left h1 (by positivity)
  · intro s hs1 hs2 hs3
    refine hz s ?_
    have hlog : Real.log (q * (|s.im| + 3)) ≤ H := by
      rw [hH]
      exact Real.log_le_log (by positivity) (by
        have : (q : ℝ) ≥ 1 := by exact_mod_cast hq1
        exact mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    have hlogpos : 0 < Real.log (q * (|s.im| + 3)) := by
      have := log_mul_abs_add_three_gt_one hq1 s.im
      linarith
    have : a ≤ c / Real.log (q * (|s.im| + 3)) := by
      rw [ha]; exact div_le_div_of_nonneg_left hc.le hlogpos hlog
    linarith
  · intro t
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp; linarith)
  · exact logDeriv_L_rect hχ hc hc2 hz hT hH ha
  · intro t _
    have hre : ((((1 + a / 4 : ℝ) : ℂ)) + t * I).re = 1 + a / 4 := by simp
    have h := logDeriv_L_line χ (s := (((1 + a / 4 : ℝ) : ℂ)) + t * I) (by rw [hre]; linarith)
      (by rw [hre]; linarith)
    rw [hre] at h
    refine h.trans ?_
    have hc0 : c ≠ 0 := hc.ne'
    have hH0 : H ≠ 0 := by linarith
    have e : 8 / (1 + a / 4 - 1) ^ 2 = 128 * H ^ 2 / c ^ 2 := by
      have h14 : 1 + a / 4 - 1 = a / 4 := by ring
      rw [h14, ha]; field_simp; ring
    rw [e, hB]
    gcongr
    norm_num

/-- **The Riesz mean of a nonprincipal character**, uniformly in the modulus up to
`exp √(log y)`: `‖∑_{n ≤ y} χ(n)Λ(n)(y-n)‖ ≤ y² exp (-c₁ √(log y))`. -/
theorem riesz_nonprincipal_sw (hZ : ClassicalZeroFreeRegion) (hS : NoSiegelZero) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ y₀ : ℝ, 1 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y → ∀ (q : ℕ) [NeZero q],
      Real.log q ≤ √(Real.log y) → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, χ n * (Λ n : ℂ) * ((y : ℂ) - n)‖ ≤
          y ^ 2 * Real.exp (-(c₁ * √(Real.log y))) := by
  obtain ⟨c, hc, hc2, hzero⟩ := zeroFree_nonprincipal hZ hS
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp
    (Fplus31.eventually_poly_le_exp 2 (3 * (666 * 16) / c ^ 2) (c / 16) (by positivity))
  set u₁ : ℝ := max u₀ 2 with hu₁
  have hu₁2 : 2 ≤ u₁ := le_max_right _ _
  refine ⟨c / 16, by positivity, Real.exp (u₁ ^ 2), Real.one_le_exp (by positivity), ?_⟩
  intro y hy q _ hqy χ hχ
  have hy1 : 1 ≤ y := le_trans (Real.one_le_exp (by positivity)) hy
  have hy0 : 0 < y := by linarith
  have hlogy : u₁ ^ 2 ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos _) hy
    rwa [Real.log_exp] at this
  set u : ℝ := √(Real.log y) with hu
  have hlog : Real.log y = u ^ 2 := by
    rw [hu, Real.sq_sqrt ((sq_nonneg _).trans hlogy)]
  have hu1 : u₁ ≤ u := by
    rw [hu]
    exact Real.le_sqrt_of_sq_le hlogy
  have hu2 : 2 ≤ u := le_trans hu₁2 hu1
  have hu0u : u₀ ≤ u := le_trans (le_max_left _ _) hu1
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hT1 : 1 ≤ Real.exp u := Real.one_le_exp (by linarith)
  have hH1 := le_log_mul_add_four hq1 u
  have hH2 := log_mul_add_four_le hq1 hu2 hqy
  set H : ℝ := Real.log (q * (Real.exp u + 4)) with hH
  have hparam := riesz_L_param hχ hc hc2 (hzero q χ hχ) (T := Real.exp u) (H := H) (a := c / H)
    hT1 hH rfl hy1
  have hB0 : 0 ≤ 666 * H ^ 2 / c ^ 2 := by positivity
  have hB : 666 * H ^ 2 / c ^ 2 ≤ (666 * 16) * u ^ 2 / c ^ 2 := by
    have hHsq : H ^ 2 ≤ (4 * u) ^ 2 := pow_le_pow_left₀ (by linarith) hH2 2
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hbud := budget_bound (c := c) (u := u) (H := H) (a := c / H) (y := y)
    (B := 666 * H ^ 2 / c ^ 2) (K := 666 * 16) hc hc2 hy1 hu2 hlog hH1 hH2 rfl hB0 hB
  refine hparam.trans (hbud.trans ?_)
  have hpoly := hu₀ u hu0u
  have hfac : 3 * ((666 * 16) * u ^ 2 / c ^ 2) ≤ Real.exp (c / 16 * u) := by
    refine le_trans (le_of_eq ?_) hpoly
    ring
  calc 3 * ((666 * 16) * u ^ 2 / c ^ 2) * y ^ 2 * Real.exp (-(c * u / 8))
      = (3 * ((666 * 16) * u ^ 2 / c ^ 2) * Real.exp (-(c * u / 8))) * y ^ 2 := by ring
    _ ≤ (Real.exp (c / 16 * u) * Real.exp (-(c * u / 8))) * y ^ 2 := by
        gcongr
    _ = y ^ 2 * Real.exp (-(c / 16 * u)) := by
        rw [← Real.exp_add]; ring_nf

end PrimeCarleson.Proof.Fplus31.PNTSW
