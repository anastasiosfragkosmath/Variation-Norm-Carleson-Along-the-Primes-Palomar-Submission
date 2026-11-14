module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Perron
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Riesz-Perron integral over a truncated rectangle

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The line integral of the Perron formula `PNTSW.Perron.riesz_formula` on
`re s = σ₁` is split at height `T`: the part with `|t| ≤ T` is moved to the line `re s = σ₀ < σ₁` by
Cauchy's theorem for a rectangle (Mathlib
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), the part with `|t| > T` is bounded
trivially. No contour shift on an infinite strip, no Gaussian regulator.

`perron_rect_bound`: for `F` entire and zero-free on the rectangle `σ₀ ≤ re s ≤ σ₁`, `|im s| ≤ T`
with `‖F'/F‖ ≤ B₁` there, and `‖F'/F(σ₁ + it)‖ ≤ B₂` for `|t| ≥ T`,

`‖∫ rieszIntegrand F y (σ₁ + it) dt‖ ≤ 4π B₁ y^{σ₀+1} + 2(σ₁-σ₀) B₁ y^{σ₁+1} / T² +
  2 B₂ y^{σ₁+1} / T`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set
open scoped Real Interval

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- `‖s‖ ‖s+1‖ ≥ (re s)² + (im s)²` for `re s ≥ 0`. -/
theorem sq_add_sq_le_norm_mul_norm {s : ℂ} (hs : 0 ≤ s.re) :
    s.re ^ 2 + s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
  have hn1 : s.re ^ 2 + s.im ^ 2 = ‖s‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn2 : ‖s‖ ≤ ‖s + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith
  have := mul_le_mul_of_nonneg_left hn2 (norm_nonneg s)
  nlinarith [this, hn1]

/-- Pointwise bound of the Riesz-Perron integrand from a bound of the logarithmic derivative. -/
theorem norm_rieszIntegrand_le_of {F : ℂ → ℂ} {y B : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re)
    (hB : ‖deriv F s / F s‖ ≤ B) :
    ‖rieszIntegrand F y s‖ ≤ B * y ^ (s.re + 1) / (s.re ^ 2 + s.im ^ 2) := by
  have hpos : 0 < s.re ^ 2 + s.im ^ 2 := by positivity
  have hden := sq_add_sq_le_norm_mul_norm hs.le
  have hcpow : ‖(y : ℂ) ^ (s + 1)‖ = y ^ (s.re + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hk : ‖(y : ℂ) ^ (s + 1) / (s * (s + 1))‖ = y ^ (s.re + 1) / (‖s‖ * ‖s + 1‖) := by
    rw [norm_div, norm_mul, hcpow]
  unfold rieszIntegrand rieszKernel
  rw [norm_mul, norm_neg, hk]
  have hmul_pos : 0 < ‖s‖ * ‖s + 1‖ := lt_of_lt_of_le hpos hden
  calc ‖deriv F s / F s‖ * (y ^ (s.re + 1) / (‖s‖ * ‖s + 1‖))
      ≤ B * (y ^ (s.re + 1) / (s.re ^ 2 + s.im ^ 2)) := by
        refine mul_le_mul hB ?_ (by positivity) hB0
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) hpos hden
    _ = _ := by ring

/-- The Riesz-Perron integrand is holomorphic where `F ≠ 0`, `re s > 0`. -/
theorem differentiableAt_rieszIntegrand {F : ℂ → ℂ} (hF : Differentiable ℂ F) {y : ℝ}
    (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) (h0 : F s ≠ 0) :
    DifferentiableAt ℂ (rieszIntegrand F y) s := by
  have hLd : DifferentiableAt ℂ (deriv F) s :=
    (hF.differentiableOn.deriv isOpen_univ).differentiableAt
      (IsOpen.mem_nhds isOpen_univ (mem_univ s))
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  unfold rieszIntegrand rieszKernel
  refine ((hLd.div (hF s) h0).neg.mul ?_)
  refine DifferentiableAt.div ?_ (differentiableAt_id.mul (differentiableAt_id.add_const 1))
    (mul_ne_zero hs0 hs1)
  exact (differentiableAt_id.add_const 1).const_cpow (Or.inl (by exact_mod_cast hy.ne'))

/-- `∫_{-T}^{T} dt/(1+t²) ≤ π`. -/
theorem integral_inv_one_add_sq_interval_le (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, (1 + t ^ 2)⁻¹ ≤ π := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc ∫ t in Ioc (-T) T, (1 + t ^ 2)⁻¹ ≤ ∫ t : ℝ, (1 + t ^ 2)⁻¹ :=
        setIntegral_le_integral integrable_inv_one_add_sq
          (Filter.Eventually.of_forall fun t => by positivity)
    _ = π := integral_univ_inv_one_add_sq

/-- `∫_{|t| > T} dt/(1+t²) ≤ 2/T`. -/
theorem tail_inv_one_add_sq_le {T : ℝ} (hT : 0 < T) :
    ∫ t in (Icc (-T) T)ᶜ, (1 + t ^ 2)⁻¹ ≤ 2 / T := by
  have h1 : ∫ t in (Icc (-T) T)ᶜ, (1 + t ^ 2)⁻¹ = π - ∫ t in Icc (-T) T, (1 + t ^ 2)⁻¹ := by
    have := integral_add_compl (measurableSet_Icc : MeasurableSet (Icc (-T) T))
      (integrable_inv_one_add_sq : Integrable fun t : ℝ => (1 + t ^ 2)⁻¹)
    rw [integral_univ_inv_one_add_sq] at this
    linarith
  have h2 : ∫ t in Icc (-T) T, (1 + t ^ 2)⁻¹ = 2 * Real.arctan T := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      integral_inv_one_add_sq, Real.arctan_neg]
    ring
  rw [h1, h2]
  have h3 := Real.arctan_inv_of_pos hT
  have h4 := Real.arctan_le_self (inv_nonneg.2 hT.le)
  have h5 : π - 2 * Real.arctan T = 2 * Real.arctan T⁻¹ := by rw [h3]; ring
  rw [h5]
  have : 2 * Real.arctan T⁻¹ ≤ 2 * T⁻¹ := by linarith
  rw [div_eq_mul_inv]
  exact this

/-- **The truncated Riesz-Perron integral.**  `F` entire and zero-free on the rectangle
`σ₀ ≤ re s ≤ σ₁`, `|im s| ≤ T` and on the line `re s = σ₁`, `‖F'/F‖ ≤ B₁` on the rectangle and
`‖F'/F(σ₁ + it)‖ ≤ B₂` for `|t| ≥ T`:

`‖∫ rieszIntegrand F y (σ₁ + it) dt‖ ≤ 4π B₁ y^{σ₀+1} + 2 (σ₁-σ₀) B₁ y^{σ₁+1}/T² +
  2 B₂ y^{σ₁+1}/T`. -/
theorem perron_rect_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {y σ₀ σ₁ T B₁ B₂ : ℝ}
    (hy : 1 ≤ y) (hσ₀ : 1 / 2 ≤ σ₀) (hσσ : σ₀ ≤ σ₁) (hσ₁ : 1 < σ₁) (hT : 1 ≤ T)
    (hz : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → |s.im| ≤ T → F s ≠ 0)
    (hz₁ : ∀ t : ℝ, F ((σ₁ : ℂ) + t * I) ≠ 0)
    (h₁ : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → |s.im| ≤ T → ‖deriv F s / F s‖ ≤ B₁)
    (h₂ : ∀ t : ℝ, T ≤ |t| → ‖deriv F ((σ₁ : ℂ) + t * I) / F ((σ₁ : ℂ) + t * I)‖ ≤ B₂) :
    ‖∫ t : ℝ, rieszIntegrand F y ((σ₁ : ℂ) + t * I)‖ ≤
      4 * π * B₁ * y ^ (σ₀ + 1) + 2 * ((σ₁ - σ₀) * B₁ * y ^ (σ₁ + 1) / T ^ 2) +
        2 * (B₂ * y ^ (σ₁ + 1) / T) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  set f : ℂ → ℂ := rieszIntegrand F y with hf
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans
    (h₁ (σ₁ : ℂ) (by simpa using hσσ) (by simp) (by simp; linarith))
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (h₂ T (by rw [abs_of_pos hT0]))
  have hpow : ∀ σ : ℝ, σ ≤ σ₁ → y ^ (σ + 1) ≤ y ^ (σ₁ + 1) := fun σ h =>
    Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have hY0 : ∀ σ : ℝ, 0 ≤ y ^ (σ + 1) := fun σ => Real.rpow_nonneg hy0.le _
  have hre : ∀ t : ℝ, ((σ₁ : ℂ) + t * I).re = σ₁ := fun t => by simp
  have him : ∀ t : ℝ, ((σ₁ : ℂ) + t * I).im = t := fun t => by simp
  -- bound on the line `re s = σ₁`
  have hsq : ∀ t : ℝ, (1 + t ^ 2)⁻¹ ≥ (σ₁ ^ 2 + t ^ 2)⁻¹ := fun t =>
    inv_anti₀ (by positivity) (by nlinarith)
  have hlineB : ∀ t : ℝ, ∀ B : ℝ, 0 ≤ B → ‖deriv F ((σ₁ : ℂ) + t * I) /
      F ((σ₁ : ℂ) + t * I)‖ ≤ B → ‖f ((σ₁ : ℂ) + t * I)‖ ≤ B * y ^ (σ₁ + 1) * (1 + t ^ 2)⁻¹ := by
    intro t B hB hle
    have := norm_rieszIntegrand_le_of (F := F) hy0 (s := (σ₁ : ℂ) + t * I)
      (by rw [hre]; linarith) hle
    rw [hre, him] at this
    refine this.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hsq t) (mul_nonneg hB (hY0 _))
  have hline : ∀ t : ℝ, ‖f ((σ₁ : ℂ) + t * I)‖ ≤
      (B₁ + B₂) * y ^ (σ₁ + 1) * (1 + t ^ 2)⁻¹ := by
    intro t
    have hk : 0 ≤ y ^ (σ₁ + 1) * (1 + t ^ 2)⁻¹ := by positivity
    rcases le_total |t| T with h | h
    · have := hlineB t B₁ hB₁0 (h₁ _ (by rw [hre]; exact hσσ) (by rw [hre]) (by rw [him]; exact h))
      refine this.trans ?_
      nlinarith [mul_nonneg hB₂0 hk]
    · have := hlineB t B₂ hB₂0 (h₂ t h)
      refine this.trans ?_
      nlinarith [mul_nonneg hB₁0 hk]
  -- continuity and integrability on the line
  have hcont : Continuous fun t : ℝ => f ((σ₁ : ℂ) + t * I) := by
    rw [continuous_iff_continuousAt]; intro t
    have h1 := (differentiableAt_rieszIntegrand hF hy0 (s := (σ₁ : ℂ) + t * I)
      (by rw [hre]; linarith) (hz₁ t)).continuousAt
    have hg : Continuous (fun t : ℝ => (σ₁ : ℂ) + t * I) := by fun_prop
    exact ContinuousAt.comp (f := fun t : ℝ => (σ₁ : ℂ) + t * I) (g := f) h1 hg.continuousAt
  have hint : Integrable fun t : ℝ => f ((σ₁ : ℂ) + t * I) :=
    (integrable_inv_one_add_sq.const_mul ((B₁ + B₂) * y ^ (σ₁ + 1))).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
        refine (hline t).trans (le_of_eq ?_); ring)
  -- split the line at `|t| = T`
  have hsplit := integral_add_compl (measurableSet_Icc : MeasurableSet (Icc (-T) T)) hint
  rw [← hsplit]
  -- the tail
  have htail : ‖∫ t in (Icc (-T) T)ᶜ, f ((σ₁ : ℂ) + t * I)‖ ≤ 2 * (B₂ * y ^ (σ₁ + 1) / T) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hS : MeasurableSet (Icc (-T) T)ᶜ := measurableSet_Icc.compl
    calc ∫ t in (Icc (-T) T)ᶜ, ‖f ((σ₁ : ℂ) + t * I)‖
        ≤ ∫ t in (Icc (-T) T)ᶜ, B₂ * y ^ (σ₁ + 1) * (1 + t ^ 2)⁻¹ := by
          refine setIntegral_mono_on hint.norm.integrableOn
            (integrable_inv_one_add_sq.const_mul _).integrableOn hS fun t ht => ?_
          have : T ≤ |t| := by
            by_contra hc
            push Not at hc
            exact ht (mem_Icc.mpr (abs_le.mp hc.le))
          exact hlineB t B₂ hB₂0 (h₂ t this)
      _ = B₂ * y ^ (σ₁ + 1) * ∫ t in (Icc (-T) T)ᶜ, (1 + t ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ B₂ * y ^ (σ₁ + 1) * (2 / T) :=
          mul_le_mul_of_nonneg_left (tail_inv_one_add_sq_le hT0) (mul_nonneg hB₂0 (hY0 _))
      _ = _ := by ring
  -- the rectangle
  have hdiff : DifferentiableOn ℂ f ([[σ₀, σ₁]] ×ℂ [[-T, T]]) := by
    intro s hs
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hσσ, Set.uIcc_of_le (by linarith)] at hs
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hs
    exact (differentiableAt_rieszIntegrand hF hy0 (by linarith)
      (hz s h1 h2 (abs_le.mpr ⟨h3, h4⟩))).differentiableWithinAt
  have hrect : (∫ x : ℝ in σ₀..σ₁, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in σ₀..σ₁, f ((x : ℂ) + (T : ℂ) * I)) +
      I • (∫ t : ℝ in (-T)..T, f ((σ₁ : ℂ) + (t : ℂ) * I)) -
      I • (∫ t : ℝ in (-T)..T, f ((σ₀ : ℂ) + (t : ℂ) * I)) = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨σ₀, -T⟩ ⟨σ₁, T⟩ hdiff
  set A : ℂ := ∫ t : ℝ in (-T)..T, f ((σ₁ : ℂ) + (t : ℂ) * I) with hA
  set Bl : ℂ := ∫ t : ℝ in (-T)..T, f ((σ₀ : ℂ) + (t : ℂ) * I) with hBl
  set Ctop : ℂ := ∫ x : ℝ in σ₀..σ₁, f ((x : ℂ) + (T : ℂ) * I) with hCtop
  set Cbot : ℂ := ∫ x : ℝ in σ₀..σ₁, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hCbot
  -- horizontal segments
  have hhoriz : ∀ τ : ℝ, |τ| = T → ∀ x ∈ Ι σ₀ σ₁, ‖f ((x : ℂ) + (τ : ℂ) * I)‖ ≤
      B₁ * y ^ (σ₁ + 1) / T ^ 2 := by
    intro τ hτ x hx
    rw [Set.uIoc_of_le hσσ] at hx
    have hxs : ((x : ℂ) + (τ : ℂ) * I).re = x := by simp
    have hxi : ((x : ℂ) + (τ : ℂ) * I).im = τ := by simp
    have hb := h₁ ((x : ℂ) + (τ : ℂ) * I) (by rw [hxs]; exact hx.1.le) (by rw [hxs]; exact hx.2)
      (by rw [hxi, hτ])
    have := norm_rieszIntegrand_le_of (F := F) hy0 (s := (x : ℂ) + (τ : ℂ) * I)
      (by rw [hxs]; linarith [hx.1]) hb
    rw [hxs, hxi] at this
    refine this.trans ?_
    have hτ2 : τ ^ 2 = T ^ 2 := by rw [← sq_abs, hτ]
    rw [hτ2]
    have hx0 : 0 ≤ x ^ 2 := sq_nonneg x
    calc B₁ * y ^ (x + 1) / (x ^ 2 + T ^ 2) ≤ B₁ * y ^ (x + 1) / T ^ 2 :=
          div_le_div_of_nonneg_left (mul_nonneg hB₁0 (hY0 _)) (by positivity) (by linarith)
      _ ≤ B₁ * y ^ (σ₁ + 1) / T ^ 2 := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hpow x hx.2) hB₁0
  have hCt : ‖Ctop‖ ≤ B₁ * y ^ (σ₁ + 1) / T ^ 2 * (σ₁ - σ₀) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₀) (b := σ₁)
      (f := fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)) (hhoriz T (abs_of_pos hT0))
    rwa [abs_of_nonneg (by linarith : 0 ≤ σ₁ - σ₀)] at this
  have hCb : ‖Cbot‖ ≤ B₁ * y ^ (σ₁ + 1) / T ^ 2 * (σ₁ - σ₀) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₀) (b := σ₁)
      (f := fun x : ℝ => f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      (hhoriz (-T) (by rw [abs_neg, abs_of_pos hT0]))
    rwa [abs_of_nonneg (by linarith : 0 ≤ σ₁ - σ₀)] at this
  -- the left line
  have hleft : ‖Bl‖ ≤ 4 * π * B₁ * y ^ (σ₀ + 1) := by
    have hbd : ∀ t ∈ Ioc (-T) T, ‖f ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤
        4 * B₁ * y ^ (σ₀ + 1) * (1 + t ^ 2)⁻¹ := by
      intro t ht
      have hts : ((σ₀ : ℂ) + (t : ℂ) * I).re = σ₀ := by simp
      have hti : ((σ₀ : ℂ) + (t : ℂ) * I).im = t := by simp
      have hb := h₁ ((σ₀ : ℂ) + (t : ℂ) * I) (by rw [hts]) (by rw [hts]; exact hσσ)
        (by rw [hti]; exact abs_le.mpr ⟨ht.1.le, ht.2⟩)
      have := norm_rieszIntegrand_le_of (F := F) hy0 (s := (σ₀ : ℂ) + (t : ℂ) * I)
        (by rw [hts]; linarith) hb
      rw [hts, hti] at this
      refine this.trans ?_
      have hq : (1 + t ^ 2) / 4 ≤ σ₀ ^ 2 + t ^ 2 := by nlinarith
      calc B₁ * y ^ (σ₀ + 1) / (σ₀ ^ 2 + t ^ 2)
          ≤ B₁ * y ^ (σ₀ + 1) / ((1 + t ^ 2) / 4) :=
            div_le_div_of_nonneg_left (mul_nonneg hB₁0 (hY0 _)) (by positivity) hq
        _ = 4 * B₁ * y ^ (σ₀ + 1) * (1 + t ^ 2)⁻¹ := by field_simp
    have hg : IntervalIntegrable (fun t : ℝ => 4 * B₁ * y ^ (σ₀ + 1) * (1 + t ^ 2)⁻¹)
        volume (-T) T :=
      (integrable_inv_one_add_sq.const_mul (4 * B₁ * y ^ (σ₀ + 1))).intervalIntegrable
    have := intervalIntegral.norm_integral_le_of_norm_le (a := -T) (b := T) (by linarith)
      (Filter.Eventually.of_forall hbd) hg
    refine this.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have := integral_inv_one_add_sq_interval_le T hT0.le
    have h4 : 0 ≤ 4 * B₁ * y ^ (σ₀ + 1) := by have := hY0 σ₀; positivity
    calc 4 * B₁ * y ^ (σ₀ + 1) * ∫ t in (-T)..T, (1 + t ^ 2)⁻¹
        ≤ 4 * B₁ * y ^ (σ₀ + 1) * π := mul_le_mul_of_nonneg_left this h4
      _ = _ := by ring
  have hAB : ‖A - Bl‖ ≤ 2 * (B₁ * y ^ (σ₁ + 1) / T ^ 2 * (σ₁ - σ₀)) := by
    have e : I • (A - Bl) = Ctop - Cbot := by
      rw [smul_sub]
      linear_combination hrect
    have : ‖A - Bl‖ = ‖Ctop - Cbot‖ := by
      rw [← e, norm_smul, Complex.norm_I, one_mul]
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    linarith
  -- assemble
  have hmain : ‖∫ t in Icc (-T) T, f ((σ₁ : ℂ) + t * I)‖ ≤
      4 * π * B₁ * y ^ (σ₀ + 1) + 2 * ((σ₁ - σ₀) * B₁ * y ^ (σ₁ + 1) / T ^ 2) := by
    have e : ∫ t in Icc (-T) T, f ((σ₁ : ℂ) + t * I) = A := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    rw [e]
    have : A = Bl + (A - Bl) := by ring
    calc ‖A‖ = ‖Bl + (A - Bl)‖ := by rw [← this]
      _ ≤ ‖Bl‖ + ‖A - Bl‖ := norm_add_le _ _
      _ ≤ _ := by
        have : 2 * (B₁ * y ^ (σ₁ + 1) / T ^ 2 * (σ₁ - σ₀)) =
            2 * ((σ₁ - σ₀) * B₁ * y ^ (σ₁ + 1) / T ^ 2) := by ring
        linarith
  calc ‖(∫ t in Icc (-T) T, f ((σ₁ : ℂ) + t * I)) + ∫ t in (Icc (-T) T)ᶜ, f ((σ₁ : ℂ) + t * I)‖
      ≤ ‖∫ t in Icc (-T) T, f ((σ₁ : ℂ) + t * I)‖ +
        ‖∫ t in (Icc (-T) T)ᶜ, f ((σ₁ : ℂ) + t * I)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end PrimeCarleson.Proof.Fplus31.PNTSW
