module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Landau
public import PrimeCarleson.Proof.Fplus31.PNTSW.Bounds
public import PrimeCarleson.Proof.Fplus31.PNT.PolyBound

/-!
# The logarithmic derivative of `L(s, χ)` near the `1`-line, from the zero-free region

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). For `F` holomorphic with zero-free region of width `a` around the `1`-line up
to height `T`, the Landau-type bound `PNTSW.Landau.logDeriv_bound_of_disc` on discs of radius `5a/4`
centered at `1 + a/4 + it` bounds `F'/F` on the strip `1 - a/2 ≤ re s ≤ 1 + a/4`, `|im s| ≤ T`:

* `logDeriv_rect` (generic): `‖F'/F‖ ≤ (112 M + 120 A) / (5a/4)`;
* `logDeriv_L_rect`: for a nonprincipal character `χ` modulo `q`, with `H = log (q (T + 4))`
  and `a = c / H`: `‖L'/L(s, χ)‖ ≤ 666 H² / c²` there;
* `logDeriv_L_line`: `‖L'/L(σ + it, χ)‖ ≤ 8 / (σ - 1)²` for `1 < σ ≤ 2`.
-/

@[expose] public noncomputable section

open Metric Complex ArithmeticFunction LSeries

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- **The logarithmic derivative on the strip** (generic form of the Landau argument). -/
theorem logDeriv_rect {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a T M A : ℝ} (ha : 0 < a)
    (ha2 : a ≤ 1 / 2) (hM : 0 < M) (hA : 0 ≤ A)
    (h0 : ∀ z : ℂ, 1 - a < z.re → z.re < 1 + 3 * a / 2 → |z.im| < T + 1 → F z ≠ 0)
    (hb : ∀ z : ℂ, 1 - a < z.re → z.re < 1 + 3 * a / 2 → |z.im| < T + 1 →
      ‖F z‖ ≤ Real.exp M)
    (hm : ∀ t : ℝ, |t| ≤ T → ∃ m : ℂ, Complex.exp m = F (((1 + a / 4 : ℝ) : ℂ) + t * I) ∧
      ‖m‖ ≤ A) :
    ∀ s : ℂ, 1 - a / 2 ≤ s.re → s.re ≤ 1 + a / 4 → |s.im| ≤ T →
      ‖deriv F s / F s‖ ≤ (112 * M + 120 * A) / (5 * a / 4) := by
  intro s hs1 hs2 hs3
  obtain ⟨m, hm1, hm2⟩ := hm s.im hs3
  set c : ℂ := ((1 + a / 4 : ℝ) : ℂ) + (s.im : ℂ) * I with hc
  have hcre : c.re = 1 + a / 4 := by simp [hc]
  have hcim : c.im = s.im := by simp [hc]
  have hball : ∀ z ∈ ball c (5 * a / 4), 1 - a < z.re ∧ z.re < 1 + 3 * a / 2 ∧ |z.im| < T + 1 := by
    intro z hz
    have hn : ‖z - c‖ < 5 * a / 4 := by simpa [mem_ball, dist_eq_norm] using hz
    have h1 := Complex.abs_re_le_norm (z - c)
    have h2 := Complex.abs_im_le_norm (z - c)
    simp only [Complex.sub_re, Complex.sub_im, hcre, hcim] at h1 h2
    have h1' := abs_lt.mp (h1.trans_lt hn)
    have h2' := abs_lt.mp (h2.trans_lt hn)
    refine ⟨by linarith [h1'.1], by linarith [h1'.2], ?_⟩
    rw [abs_lt]
    constructor <;> linarith [abs_le.mp hs3, h2'.1, h2'.2]
  have hFd : DifferentiableOn ℂ F (ball c (5 * a / 4)) := hF.differentiableOn
  have hz0 : ∀ z ∈ ball c (5 * a / 4), F z ≠ 0 := fun z hz =>
    h0 z (hball z hz).1 (hball z hz).2.1 (hball z hz).2.2
  have hbz : ∀ z ∈ ball c (5 * a / 4), ‖F z‖ ≤ Real.exp M := fun z hz =>
    hb z (hball z hz).1 (hball z hz).2.1 (hball z hz).2.2
  have hsc : s ∈ closedBall c (3 * (5 * a / 4) / 4) := by
    rw [mem_closedBall, dist_eq_norm]
    have hss : s - c = ((s.re - (1 + a / 4) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [hss, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  exact logDeriv_bound_of_disc (by positivity) hM hA hFd hz0 hbz hm1 hm2 hsc

/-- `1 < log (q (T + 4))` for `q ≥ 1`, `T ≥ 0`. -/
theorem one_lt_log_mul_add_four {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 0 ≤ T) :
    1 < Real.log (q * (T + 4)) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h3 : (4 : ℝ) ≤ q * (T + 4) := by
    have := mul_le_mul hq' (show (4 : ℝ) ≤ T + 4 by linarith) (by norm_num) (by linarith)
    linarith only [this]
  have h4 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

/-- `L'/L = -∑ χ(n) Λ(n) n^{-s}` on `re s > 1`. -/
theorem logDeriv_LFunction_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      -LSeries (fun n : ℕ => χ n * (Λ n : ℂ)) s := by
  have h2 : LSeries (fun n : ℕ => χ n * (Λ n : ℂ)) s =
      -deriv (LSeries fun n : ℕ => (χ n : ℂ)) s / LSeries (fun n : ℕ => (χ n : ℂ)) s :=
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [h2, neg_div, neg_neg, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]

/-- The trivial bound for the logarithmic derivative on `1 < re s ≤ 2`. -/
theorem logDeriv_L_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re)
    (hs2 : s.re ≤ 2) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      8 / (s.re - 1) ^ 2 := by
  rw [logDeriv_LFunction_eq χ hs, norm_neg]
  exact norm_LSeries_twist_vonMangoldt_le χ hs hs2

/-- **The logarithmic derivative of `L(s, χ)` on the strip** `1 - a/2 ≤ re s ≤ 1 + a/4`,
`|im s| ≤ T`, for a nonprincipal `χ` whose `L`-function has no zero with
`re s ≥ 1 - c / log (q (|im s| + 3))`; `H = log (q (T + 4))`, `a = c / H`. -/
theorem logDeriv_L_rect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hz : ∀ s : ℂ, 1 - c / Real.log (q * (|s.im| + 3)) ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0)
    {T H a : ℝ} (hT : 1 ≤ T) (hH : H = Real.log (q * (T + 4))) (ha : a = c / H) :
    ∀ s : ℂ, 1 - a / 2 ≤ s.re → s.re ≤ 1 + a / 4 → |s.im| ≤ T →
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        666 * H ^ 2 / c ^ 2 := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hH1 : 1 < H := by rw [hH]; exact one_lt_log_mul_add_four hq1 (by linarith)
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [ha, div_le_iff₀ (by linarith)]; linarith
  have haH : a * H = c := by rw [ha]; field_simp
  have hB := logDeriv_rect (F := DirichletCharacter.LFunction χ)
    (DirichletCharacter.differentiable_LFunction hχ) (a := a) (T := T) (M := H + 1)
    (A := 6 / a) ha0 ha2 (by linarith) (by positivity) ?_ ?_ ?_
  · intro s h1 h2 h3
    refine (hB s h1 h2 h3).trans ?_
    have key : (112 * (H + 1) + 120 * (6 / a)) / (5 * a / 4) =
        4 * H * (112 * (H + 1) * c + 720 * H) / (5 * c ^ 2) := by
      rw [ha]; field_simp; ring
    rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 112 * (H + 1) * c ≤ 112 * H := by
      have := mul_le_mul_of_nonneg_left hc2 (by linarith only [hH1] : (0 : ℝ) ≤ H)
      linarith only [this, hc2, hH1]
    have h5 : 4 * H * (112 * (H + 1) * c + 720 * H) ≤ 666 * H ^ 2 * 5 := by
      have := mul_le_mul_of_nonneg_left h4 (by linarith only [hH1] : (0 : ℝ) ≤ 4 * H)
      linarith only [this, sq_nonneg H]
    linarith [mul_le_mul_of_nonneg_right h5 (sq_nonneg c)]
  · intro z hz1 hz2 hz3
    refine hz z ?_
    have hlog : Real.log (q * (|z.im| + 3)) ≤ H := by
      rw [hH]
      exact Real.log_le_log (by positivity)
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    have hlogpos : 0 < Real.log (q * (|z.im| + 3)) := by
      have := log_mul_abs_add_three_gt_one hq1 z.im
      linarith
    have : a ≤ c / Real.log (q * (|z.im| + 3)) := by
      rw [ha]; exact div_le_div_of_nonneg_left hc.le hlogpos hlog
    linarith
  · intro z hz1 hz2 hz3
    have hre : (1 / 2 : ℝ) < z.re := by linarith
    have hnorm := norm_LFunction_le hχ (s := z) (by linarith)
    have hzn : ‖z‖ ≤ T + 3 := by
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos (by linarith : 0 < z.re)] at h1
      linarith
    have h5 : ‖DirichletCharacter.LFunction χ z‖ ≤ 2 * (q * (T + 3)) := by
      refine hnorm.trans ?_
      rw [div_le_iff₀ (by linarith)]
      have : (q : ℝ) * ‖z‖ ≤ q * (T + 3) := mul_le_mul_of_nonneg_left hzn (by linarith)
      linarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ q) (by linarith : (0 : ℝ) ≤ T + 3))
        (by linarith : (0 : ℝ) ≤ 2 * z.re - 1)]
    refine h5.trans ?_
    have hexp : Real.exp (H + 1) = Real.exp 1 * (q * (T + 4)) := by
      rw [Real.exp_add, hH, Real.exp_log (by positivity), mul_comm]
    rw [hexp]
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hq4 : 0 ≤ (q : ℝ) * (T + 4) := mul_nonneg (by linarith) (by linarith)
    have h6 := mul_le_mul_of_nonneg_right he hq4
    have h7 : (q : ℝ) * (T + 3) ≤ q * (T + 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith only [h6, h7]
  · intro t ht
    set z₀ : ℂ := ((1 + a / 4 : ℝ) : ℂ) + t * I with hz₀
    have hre : 1 < z₀.re := by simp [hz₀]; linarith
    refine ⟨LSeries (fun n : ℕ => χ n * (Λ n : ℂ) / (Real.log n : ℂ)) z₀, ?_, ?_⟩
    · rw [DirichletCharacter.LSeries_eq_exp_LSeries χ hre,
        DirichletCharacter.LFunction_eq_LSeries χ hre]
    · refine (norm_eulerLog_le χ hre).trans ?_
      have hre' : z₀.re = 1 + a / 4 := by simp [hz₀]
      rw [hre']
      have e : (1 + a / 4) / (1 + a / 4 - 1) + 1 = 4 / a + 2 := by
        have h14 : 1 + a / 4 - 1 = a / 4 := by ring
        rw [h14]; field_simp; ring
      rw [e]
      have : 2 ≤ 2 / a := by rw [le_div_iff₀ ha0]; linarith
      have e2 : 6 / a = 4 / a + 2 / a := by ring
      linarith

end PrimeCarleson.Proof.Fplus31.PNTSW
