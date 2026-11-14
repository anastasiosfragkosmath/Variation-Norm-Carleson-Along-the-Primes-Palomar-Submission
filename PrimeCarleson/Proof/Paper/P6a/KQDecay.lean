module

public import PrimeCarleson.Proof.Paper.P6a.KQConv

/-!
# Decay of the `K_Q`-replacement error kernel

Source: main paper `p:red-var`, L1504: with `H = ∑_{k ≥ k₀} ψ_k` and `E = errW = H - φ_N * H`,
`E(n) = ∫ φ_N(y) (H(n) - H(n - y)) dy`, so
* `|E(n)| ≤ (4/3) L 4^{-k₀} N m₁` for all `n` (`H` is Lipschitz), and
* `|E(n)| ≤ (2 N m₁ + (2 + 8B) 2^{-k₀} N² m₂) / n²` for `|n| ≥ 2^{k₀+1}` (`H(t) = 1/t` for
  `|t| ≥ 2^{k₀}`),
with `m_j = ∫ |u|^j |φ(u)| du`, `N = N(Q)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

variable (S : KQSetup)

/-- The moment `m_k = ∫ |u|^k |φ(u)| du` of the cutoff. -/
def phiMoment (k : ℕ) : ℝ := ∫ u : ℝ, ‖u‖ ^ k * ‖(S.φ.toSchwartz : ℝ → ℂ) u‖

theorem phiMoment_nonneg (k : ℕ) : 0 ≤ phiMoment S k :=
  integral_nonneg fun _ => by positivity

/-- `|φ_N(y)| = N⁻¹ |φ(y/N)|`. -/
theorem norm_phiN (Q : ℕ) (y : ℝ) :
    ‖phiN S Q y‖ = (S.P.NQ Q)⁻¹ * ‖(S.φ.toSchwartz : ℝ → ℂ) (y / S.P.NQ Q)‖ := by
  have hN := S.P.NQ_pos Q
  simp only [phiN, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hN]

theorem norm_eq_mul_norm_div (Q : ℕ) (y : ℝ) : ‖y‖ = S.P.NQ Q * ‖y / S.P.NQ Q‖ := by
  have hN := S.P.NQ_pos Q
  rw [norm_div, Real.norm_of_nonneg hN.le]
  field_simp

/-- `y ↦ |y|^k |φ_N(y)|` is integrable. -/
theorem integrable_pow_norm_phiN (Q k : ℕ) :
    Integrable fun y : ℝ => ‖y‖ ^ k * ‖phiN S Q y‖ := by
  have hN := S.P.NQ_pos Q
  have h := ((S.φ.toSchwartz.integrable_pow_mul volume k).const_mul
    ((S.P.NQ Q) ^ k * (S.P.NQ Q)⁻¹)).comp_div hN.ne'
  refine h.congr (ae_of_all _ fun y => ?_)
  change (S.P.NQ Q) ^ k * (S.P.NQ Q)⁻¹ * (‖y / S.P.NQ Q‖ ^ k * ‖(S.φ.toSchwartz : ℝ → ℂ)
    (y / S.P.NQ Q)‖) = ‖y‖ ^ k * ‖phiN S Q y‖
  rw [norm_phiN, norm_eq_mul_norm_div S Q y, mul_pow]
  simp only [norm_div, Real.norm_of_nonneg hN.le]
  ring

/-- `∫ |y|^k |φ_N(y)| dy = N^k m_k`. -/
theorem integral_pow_norm_phiN (Q k : ℕ) :
    ∫ y : ℝ, ‖y‖ ^ k * ‖phiN S Q y‖ = (S.P.NQ Q) ^ k * phiMoment S k := by
  have hN := S.P.NQ_pos Q
  have h := Measure.integral_comp_div (fun u : ℝ => (S.P.NQ Q) ^ k * (S.P.NQ Q)⁻¹ *
    (‖u‖ ^ k * ‖(S.φ.toSchwartz : ℝ → ℂ) u‖)) (S.P.NQ Q)
  have h2 : (fun y : ℝ => ‖y‖ ^ k * ‖phiN S Q y‖) = fun y : ℝ => (S.P.NQ Q) ^ k *
      (S.P.NQ Q)⁻¹ * (‖y / S.P.NQ Q‖ ^ k * ‖(S.φ.toSchwartz : ℝ → ℂ) (y / S.P.NQ Q)‖) := by
    funext y
    rw [norm_phiN, norm_eq_mul_norm_div S Q y, mul_pow]
    simp only [norm_div, Real.norm_of_nonneg hN.le]
    ring
  rw [h2]
  refine h.trans ?_
  rw [abs_of_pos hN, integral_const_mul]
  unfold phiMoment
  simp only [smul_eq_mul]
  field_simp

/-- `H` is continuous (it is Lipschitz). -/
theorem continuous_Hfn {B L : ℝ} (hB : ∀ t, |S.ψ.toFun t| ≤ B)
    (hL : ∀ t t', |S.ψ.toFun t - S.ψ.toFun t'| ≤ L * |t - t'|) (k₀ : ℕ) :
    Continuous (Hfn S.ψ k₀) := by
  have hL0 : 0 ≤ L := by
    have h := hL 1 0
    rw [sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  refine (LipschitzWith.of_dist_le_mul (K := ⟨4 / 3 * L * ((4 : ℝ) ^ k₀)⁻¹, by positivity⟩)
    fun t t' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  exact abs_Hfn_sub_le hB hL k₀ t t'

/-- **The error kernel as an integral against `φ_N`**:
`E_Q(n) = ∫ φ_N(y) (H(n) - H(n - y)) dy` (`∫ φ_N = 1`). -/
theorem errW_eq_integral_phiN {B L : ℝ} (hB : ∀ t, |S.ψ.toFun t| ≤ B)
    (hL : ∀ t t', |S.ψ.toFun t - S.ψ.toFun t'| ≤ L * |t - t'|) (Q : ℕ) (n : ℤ) :
    errW S Q n = ∫ y : ℝ, phiN S Q y * ((Hfn S.ψ (S.P.kmin Q) (n : ℝ) -
      Hfn S.ψ (S.P.kmin Q) ((n : ℝ) - y) : ℝ) : ℂ) := by
  set k₀ := S.P.kmin Q with hk₀
  have hHc := continuous_Hfn S hB hL k₀
  have hi1 : Integrable fun y : ℝ => phiN S Q y * ((Hfn S.ψ k₀ (n : ℝ) : ℝ) : ℂ) :=
    (integrable_phiN S Q).mul_const _
  have hi2 : Integrable fun y : ℝ => phiN S Q y * ((Hfn S.ψ k₀ ((n : ℝ) - y) : ℝ) : ℂ) := by
    refine (integrable_phiN S Q).mul_bdd (c := 2 * B * ((2 : ℝ) ^ k₀)⁻¹) ?_
      (ae_of_all _ fun y => ?_)
    · exact (Complex.continuous_ofReal.comp
        (hHc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_Hfn_le hB k₀ _
  have h1 : ((Hfn S.ψ k₀ (n : ℝ) : ℝ) : ℂ) =
      ∫ y : ℝ, phiN S Q y * ((Hfn S.ψ k₀ (n : ℝ) : ℝ) : ℂ) := by
    rw [integral_mul_const, integral_phiN, one_mul]
  have h2 := KQz_eq_conv S Q n
  unfold errW
  rw [psiTailZ_eq_Hfn, h2]
  conv_lhs => rw [h1]
  rw [← integral_sub hi1 hi2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  push_cast
  ring

/-- **Global bound**: `|E_Q(n)| ≤ (4/3) L 4^{-k₀} N m₁` for every `n`. -/
theorem norm_errW_le_global {B L : ℝ} (hB : ∀ t, |S.ψ.toFun t| ≤ B)
    (hL : ∀ t t', |S.ψ.toFun t - S.ψ.toFun t'| ≤ L * |t - t'|) (Q : ℕ) (n : ℤ) :
    ‖errW S Q n‖ ≤ 4 / 3 * L * ((4 : ℝ) ^ (S.P.kmin Q))⁻¹ * (S.P.NQ Q * phiMoment S 1) := by
  set k₀ := S.P.kmin Q with hk₀
  set K : ℝ := 4 / 3 * L * ((4 : ℝ) ^ k₀)⁻¹ with hK
  have hL0 : 0 ≤ L := by
    have h := hL 1 0
    rw [sub_zero, abs_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hK0 : 0 ≤ K := by positivity
  rw [errW_eq_integral_phiN S hB hL Q n]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hmaj : Integrable fun y : ℝ => K * (‖y‖ ^ 1 * ‖phiN S Q y‖) :=
    (integrable_pow_norm_phiN S Q 1).const_mul K
  calc ∫ y : ℝ, ‖phiN S Q y * ((Hfn S.ψ k₀ (n : ℝ) - Hfn S.ψ k₀ ((n : ℝ) - y) : ℝ) : ℂ)‖
      ≤ ∫ y : ℝ, K * (‖y‖ ^ 1 * ‖phiN S Q y‖) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _) hmaj
          (ae_of_all _ fun y => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h := abs_Hfn_sub_le hB hL k₀ (n : ℝ) ((n : ℝ) - y)
        rw [sub_sub_cancel, ← Real.norm_eq_abs y] at h
        calc ‖phiN S Q y‖ * |Hfn S.ψ k₀ (n : ℝ) - Hfn S.ψ k₀ ((n : ℝ) - y)|
            ≤ ‖phiN S Q y‖ * (K * ‖y‖) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
          _ = K * (‖y‖ ^ 1 * ‖phiN S Q y‖) := by ring
    _ = K * (S.P.NQ Q * phiMoment S 1) := by
        rw [integral_const_mul, integral_pow_norm_phiN]; ring

/-- The far-field bound for `H`: for `k₀ ≥ 1`, `|t| ≥ 2^{k₀+1}` and every `y`,
`|H(t) - H(t - y)| ≤ 2|y|/t² + (2 + 8B) 2^{-k₀} y²/t²`. -/
theorem abs_Hfn_diff_far {B : ℝ} (hB : ∀ t, |S.ψ.toFun t| ≤ B) {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {t : ℝ}
    (ht : (2 : ℝ) ^ (k₀ + 1) ≤ |t|) (y : ℝ) :
    |Hfn S.ψ k₀ t - Hfn S.ψ k₀ (t - y)| ≤
      2 * |y| / t ^ 2 + (2 + 8 * B) * ((2 : ℝ) ^ k₀)⁻¹ * y ^ 2 / t ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have ha : (0 : ℝ) < 2 ^ k₀ := by positivity
  set a : ℝ := (2 : ℝ) ^ k₀ with hadef
  have ht2 : 2 * a ≤ |t| := by
    calc 2 * a = (2 : ℝ) ^ (k₀ + 1) := by rw [pow_succ]; ring
      _ ≤ |t| := ht
  have htpos : 0 < |t| := by linarith
  have ht0 : t ≠ 0 := abs_pos.1 htpos
  have hat : a ≤ |t| := by linarith
  have hHt : Hfn S.ψ k₀ t = 1 / t := Hfn_eq_inv hk₀ hat
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have t2pos : 0 < t ^ 2 := by positivity
  have hnn1 : 0 ≤ 2 * |y| / t ^ 2 := by positivity
  have hnn2 : 0 ≤ (2 + 8 * B) * a⁻¹ * y ^ 2 / t ^ 2 := by positivity
  by_cases hy : |y| ≤ |t| / 2
  · -- near field
    have hty : |t| / 2 ≤ |t - y| := by
      have := abs_sub_abs_le_abs_sub t y
      linarith
    have hty' : a ≤ |t - y| := by linarith
    have hHty : Hfn S.ψ k₀ (t - y) = 1 / (t - y) := Hfn_eq_inv hk₀ hty'
    have hty0 : t - y ≠ 0 := by
      intro h; rw [h, abs_zero] at hty; linarith
    rw [hHt, hHty]
    have e1 : 1 / t - 1 / (t - y) = -y / (t * (t - y)) := by field_simp; ring
    rw [e1, abs_div, abs_neg, abs_mul]
    have h3 : 2 * |y| / t ^ 2 ≥ |y| / (|t| * |t - y|) := by
      rw [ge_iff_le, div_le_div_iff₀ (by positivity) t2pos]
      rw [hsq]
      nlinarith [abs_nonneg y, mul_nonneg (abs_nonneg y) (abs_nonneg t)]
    linarith
  · -- far field
    push Not at hy
    have h1 : |Hfn S.ψ k₀ t| ≤ 1 / (2 * a) := by
      rw [hHt, abs_div, abs_one]
      exact one_div_le_one_div_of_le (by positivity) ht2
    have h2 := abs_Hfn_le hB k₀ (t - y)
    have h4 : |Hfn S.ψ k₀ t - Hfn S.ψ k₀ (t - y)| ≤ (1 / 2 + 2 * B) * a⁻¹ := by
      calc |Hfn S.ψ k₀ t - Hfn S.ψ k₀ (t - y)|
          ≤ |Hfn S.ψ k₀ t| + |Hfn S.ψ k₀ (t - y)| := abs_sub _ _
        _ ≤ 1 / (2 * a) + 2 * B * a⁻¹ := add_le_add h1 h2
        _ = (1 / 2 + 2 * B) * a⁻¹ := by field_simp
    have h5 : 1 ≤ 4 * y ^ 2 / t ^ 2 := by
      rw [le_div_iff₀ t2pos, hsq]
      have : |t| < 2 * |y| := by linarith
      have h6 : |t| ^ 2 < (2 * |y|) ^ 2 := by
        exact pow_lt_pow_left₀ this (abs_nonneg _) (by norm_num)
      rw [mul_pow, sq_abs] at h6
      nlinarith [sq_abs y]
    calc |Hfn S.ψ k₀ t - Hfn S.ψ k₀ (t - y)| ≤ (1 / 2 + 2 * B) * a⁻¹ := h4
      _ ≤ (1 / 2 + 2 * B) * a⁻¹ * (4 * y ^ 2 / t ^ 2) :=
          le_mul_of_one_le_right (by positivity) h5
      _ = (2 + 8 * B) * a⁻¹ * y ^ 2 / t ^ 2 := by ring
      _ ≤ 2 * |y| / t ^ 2 + (2 + 8 * B) * a⁻¹ * y ^ 2 / t ^ 2 := by linarith

/-- **Far-field bound**: for `|n| ≥ 2^{k₀+1}`,
`|E_Q(n)| ≤ (2 N m₁ + (2 + 8B) 2^{-k₀} N² m₂) / n²`. -/
theorem norm_errW_le_far {B L : ℝ} (hB : ∀ t, |S.ψ.toFun t| ≤ B)
    (hL : ∀ t t', |S.ψ.toFun t - S.ψ.toFun t'| ≤ L * |t - t'|) {Q : ℕ} (hQ : 1 ≤ Q) (n : ℤ)
    (hn : (2 : ℝ) ^ (S.P.kmin Q + 1) ≤ |(n : ℝ)|) :
    ‖errW S Q n‖ ≤ (2 * (S.P.NQ Q * phiMoment S 1) + (2 + 8 * B) * ((2 : ℝ) ^ S.P.kmin Q)⁻¹ *
      ((S.P.NQ Q) ^ 2 * phiMoment S 2)) / (n : ℝ) ^ 2 := by
  set k₀ := S.P.kmin Q with hk₀
  have hk₁ : 1 ≤ k₀ := S.P.one_le_kmin hQ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have ht2 : 0 < (n : ℝ) ^ 2 := by
    have h1 : 0 < |(n : ℝ)| := lt_of_lt_of_le (by positivity) hn
    have h2 : (n : ℝ) ≠ 0 := abs_pos.1 h1
    positivity
  set c : ℝ := (2 + 8 * B) * ((2 : ℝ) ^ k₀)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  rw [errW_eq_integral_phiN S hB hL Q n]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hmaj : Integrable fun y : ℝ => (2 / (n : ℝ) ^ 2) * (‖y‖ ^ 1 * ‖phiN S Q y‖) +
      (c / (n : ℝ) ^ 2) * (‖y‖ ^ 2 * ‖phiN S Q y‖) :=
    ((integrable_pow_norm_phiN S Q 1).const_mul _).add
      ((integrable_pow_norm_phiN S Q 2).const_mul _)
  calc ∫ y : ℝ, ‖phiN S Q y * ((Hfn S.ψ k₀ (n : ℝ) - Hfn S.ψ k₀ ((n : ℝ) - y) : ℝ) : ℂ)‖
      ≤ ∫ y : ℝ, ((2 / (n : ℝ) ^ 2) * (‖y‖ ^ 1 * ‖phiN S Q y‖) +
          (c / (n : ℝ) ^ 2) * (‖y‖ ^ 2 * ‖phiN S Q y‖)) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _) hmaj
          (ae_of_all _ fun y => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h := abs_Hfn_diff_far S hB hk₁ hn y
        rw [← Real.norm_eq_abs y] at h
        have hy2 : ‖y‖ ^ 2 = y ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        calc ‖phiN S Q y‖ * |Hfn S.ψ k₀ (n : ℝ) - Hfn S.ψ k₀ ((n : ℝ) - y)|
            ≤ ‖phiN S Q y‖ * (2 * ‖y‖ / (n : ℝ) ^ 2 + c * y ^ 2 / (n : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left h (norm_nonneg _)
          _ = _ := by rw [← hy2]; ring
    _ = (2 / (n : ℝ) ^ 2) * (S.P.NQ Q * phiMoment S 1) +
          (c / (n : ℝ) ^ 2) * ((S.P.NQ Q) ^ 2 * phiMoment S 2) := by
        rw [integral_add ((integrable_pow_norm_phiN S Q 1).const_mul _)
          ((integrable_pow_norm_phiN S Q 2).const_mul _), integral_const_mul, integral_const_mul,
          integral_pow_norm_phiN, integral_pow_norm_phiN, pow_one]
    _ = _ := by rw [hc]; ring

end PrimeCarleson.Proof.Paper
