module

public import PrimeCarleson.Proof.Fplus31.PNTSW.PoleKernel
public import PrimeCarleson.Proof.Fplus31.PNT.PolyBound
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Polynomial bounds and trivial bounds for the Dirichlet series on `re s > 1`

Part of the prime number theorem in progressions on the classical zero-free region
(`PNTSW/Main.lean`). The polynomial bounds for `L₁ = (s-1) ζ` and the elementary bounds on
`re s > 1` needed for the logarithmic derivative:

* `norm_zetaL1_le`: `‖L₁(s)‖ ≤ ‖s‖ + ‖s‖‖s-1‖/re s` for `re s > 0` (`L₁ = (s-1)ζ`, Abel summation);
* `norm_riemannZeta_real_le`: `ζ(τ) ≤ τ/(τ-1) + 1` for real `τ > 1`;
* `norm_LSeries_le_zetaSum`: `‖∑ f(n) n^{-s}‖ ≤ K (τ/(τ-1) + 1)` if `‖f(n)‖ ≤ K n^ε`
  and `τ + ε ≤ re s`;
* `norm_eulerLog_le`: the Euler logarithm `∑ χ(n)Λ(n)/log n · n^{-s}` has norm at most
  `σ/(σ-1) + 1` (`σ = re s > 1`);
* `norm_LSeries_twist_vonMangoldt_le`: `‖∑ χ(n)Λ(n) n^{-s}‖ ≤ 8/(σ-1)²` for `1 < σ ≤ 2`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Filter Asymptotics LSeries ArithmeticFunction
open scoped Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- The fractional part, as a complex-valued function. -/
def fractFn (t : ℝ) : ℂ := ((Int.fract t : ℝ) : ℂ)

/-- The fractional part is measurable. -/
theorem fractFn_measurable : Measurable fractFn :=
  Complex.measurable_ofReal.comp measurable_fract

/-- The fractional part has norm at most `1`. -/
theorem norm_fractFn_le (t : ℝ) : ‖fractFn t‖ ≤ 1 := by
  unfold fractFn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

/-- `M(s) = ∫_1^∞ {t} t^{-(s+1)} dt`. -/
def fractIntegral (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), fractFn t * (t : ℂ) ^ (-(s + 1))

/-- `‖M(s)‖ ≤ 1 / re s` for `re s > 0`. -/
theorem norm_fractIntegral_le {s : ℂ} (hs : 0 < s.re) : ‖fractIntegral s‖ ≤ 1 / s.re :=
  norm_integral_Ioi_le fractFn 1 norm_fractFn_le hs

/-- `M` is holomorphic on `re s > 0`. -/
theorem differentiableOn_fractIntegral : DifferentiableOn ℂ fractIntegral {s : ℂ | 0 < s.re} :=
  differentiableOn_integral_Ioi fractFn fractFn_measurable 1 norm_fractFn_le

/-- Abel summation for `ζ`: `ζ(s) = s/(s-1) - s M(s)` for `re s > 1`. -/
theorem riemannZeta_eq_fractIntegral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * fractIntegral s := by
  have hs0 : 0 < s.re := by linarith
  have h1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hsum : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    simp
  have hmain := LSeries_eq_mul_integral (1 : ℕ → ℂ) (r := 1) zero_le_one hs hsum hO
  rw [← LSeries_one_eq_riemannZeta hs, hmain]
  have hsum' : ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = (⌊t⌋₊ : ℂ) := by
    intro t; simp
  have hpt : ∀ t ∈ Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(s + 1)) =
      (t : ℂ) ^ (-s) - fractFn t * (t : ℂ) ^ (-(s + 1)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have e1 : (⌊t⌋₊ : ℂ) = (t : ℂ) - fractFn t := by
      unfold fractFn
      have : (⌊t⌋₊ : ℝ) = t - Int.fract t := by
        rw [Int.fract, ← Int.natCast_floor_eq_floor ht0.le]
        push_cast
        ring
      exact_mod_cast this
    have e2 : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      calc (t : ℂ) ^ (-s) = (t : ℂ) ^ (-(s + 1) + 1) := by ring_nf
        _ = (t : ℂ) ^ (-(s + 1)) * (t : ℂ) ^ (1 : ℂ) := Complex.cpow_add _ _ htc
        _ = _ := by rw [Complex.cpow_one]; ring
    rw [hsum' t, e1, e2]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one
  have hI2 : IntegrableOn (fun t : ℝ => fractFn t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    have hc : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
      integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
    refine hc.norm.mono' (fractFn_measurable.aestronglyMeasurable.mul hc.1) ?_
    filter_upwards with t
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_fractFn_le t)
  rw [integral_sub hI1 hI2, integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one]
  unfold fractIntegral
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have : -s + 1 ≠ 0 := by
    intro h; apply h1; linear_combination -h
  field_simp
  ring

/-- `L₁(s) = s - s (s-1) M(s)` for `re s > 1`. -/
theorem zetaL1_eq_fractIntegral {s : ℂ} (hs : 1 < s.re) :
    zetaL1 s = s - s * (s - 1) * fractIntegral s := by
  have h1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [zetaL1_apply h1, riemannZeta_eq_fractIntegral hs]
  field_simp

/-- `L₁(s) = s - s (s-1) M(s)` on the whole half-plane `re s > 0` (identity theorem). -/
theorem zetaL1_eq_fractIntegral_of_pos {s : ℂ} (hs : 0 < s.re) :
    zetaL1 s = s - s * (s - 1) * fractIntegral s := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hconv : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hRd : DifferentiableOn ℂ (fun s : ℂ => s - s * (s - 1) * fractIntegral s)
      {s : ℂ | 0 < s.re} :=
    differentiableOn_id.sub ((differentiableOn_id.mul (differentiableOn_id.sub_const 1)).mul
      differentiableOn_fractIntegral)
  have hLd : DifferentiableOn ℂ zetaL1 {s : ℂ | 0 < s.re} :=
    differentiable_zetaL1.differentiableOn
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : zetaL1 =ᶠ[nhds (2 : ℂ)] fun s : ℂ => s - s * (s - 1) * fractIntegral s := by
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with z hz
    exact zetaL1_eq_fractIntegral hz
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hLd.analyticOnNhd hopen)
    (hRd.analyticOnNhd hopen) hconv h2 hev) hs

/-- **Polynomial bound for `L₁`**: `‖L₁(s)‖ ≤ ‖s‖ + ‖s‖ ‖s-1‖ / re s` for `re s > 0`. -/
theorem norm_zetaL1_le {s : ℂ} (hs : 0 < s.re) :
    ‖zetaL1 s‖ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [zetaL1_eq_fractIntegral_of_pos hs]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  rw [norm_mul, norm_mul]
  calc ‖s‖ * ‖s - 1‖ * ‖fractIntegral s‖ ≤ ‖s‖ * ‖s - 1‖ * (1 / s.re) :=
        mul_le_mul_of_nonneg_left (norm_fractIntegral_le hs) (by positivity)
    _ = _ := by ring


/-- `ζ(τ) ≤ τ/(τ-1) + 1` for real `τ > 1`. -/
theorem norm_riemannZeta_real_le {τ : ℝ} (hτ : 1 < τ) :
    ‖riemannZeta (τ : ℂ)‖ ≤ τ / (τ - 1) + 1 := by
  have hs : 1 < (τ : ℂ).re := by simpa using hτ
  have hτ0 : 0 < τ := by linarith
  rw [riemannZeta_eq_fractIntegral hs]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(τ : ℂ) / ((τ : ℂ) - 1)‖ = τ / (τ - 1) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0]
    have : ((τ : ℂ) - 1) = ((τ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h2 : ‖(τ : ℂ) * fractIntegral (τ : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0]
    have := norm_fractIntegral_le (s := (τ : ℂ)) (by simpa using hτ0)
    simp only [Complex.ofReal_re] at this
    calc τ * ‖fractIntegral (τ : ℂ)‖ ≤ τ * (1 / τ) := mul_le_mul_of_nonneg_left this hτ0.le
      _ = 1 := by field_simp
  linarith

/-- The terms `n^{-τ}` of the real zeta series sum to at most `τ/(τ-1) + 1`. -/
theorem tsum_norm_term_one_le {τ : ℝ} (hτ : 1 < τ) :
    ∑' n : ℕ, ‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ ≤ τ / (τ - 1) + 1 := by
  have hs : 1 < (τ : ℂ).re := by simpa using hτ
  have hsum : LSeriesSummable (1 : ℕ → ℂ) (τ : ℂ) := LSeriesSummable_one_iff.mpr hs
  have hterm : ∀ n : ℕ, term (1 : ℕ → ℂ) (τ : ℂ) n = ((‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have e1 : term (1 : ℕ → ℂ) (τ : ℂ) n = ((((n : ℝ) ^ τ)⁻¹ : ℝ) : ℂ) := by
        rw [LSeries.term_of_ne_zero hn, Pi.one_apply, Complex.ofReal_inv,
          Complex.ofReal_cpow hn0]
        simp
      have e2 : ‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ = ((n : ℝ) ^ τ)⁻¹ := by
        rw [e1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [e2]
      exact e1
  have h1 : LSeries (1 : ℕ → ℂ) (τ : ℂ) = ((∑' n : ℕ, ‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have h2 : ‖LSeries (1 : ℕ → ℂ) (τ : ℂ)‖ = ∑' n : ℕ, ‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ := by
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  rw [← h2, LSeries_one_eq_riemannZeta hs]
  exact norm_riemannZeta_real_le hτ

/-- **Comparison with the real zeta series.**  If `‖f n‖ ≤ K n^ε` for `n ≥ 1` and
`τ + ε ≤ re s` with `τ > 1`, then `‖∑ f(n) n^{-s}‖ ≤ K (τ/(τ-1) + 1)`. -/
theorem norm_LSeries_le_zetaSum {f : ℕ → ℂ} {K ε τ : ℝ} {s : ℂ} (hK : 0 ≤ K)
    (hτ : 1 < τ) (hs : τ + ε ≤ s.re) (hf : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ K * (n : ℝ) ^ ε) :
    ‖LSeries f s‖ ≤ K * (τ / (τ - 1) + 1) := by
  have hterm : ∀ n : ℕ, ‖term f s n‖ ≤ K * ‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [norm_term_eq, norm_term_eq]
      simp only [hn, ↓reduceIte, Pi.one_apply, norm_one, Complex.ofReal_re]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hn0 : (0 : ℝ) < n := by linarith
      have h1 : (n : ℝ) ^ τ * (n : ℝ) ^ ε ≤ (n : ℝ) ^ s.re := by
        rw [← Real.rpow_add hn0]
        exact Real.rpow_le_rpow_of_exponent_le hn1 hs
      have h2 := hf n (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
      have hpos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hn0 _
      have hpos2 : 0 < (n : ℝ) ^ τ := Real.rpow_pos_of_pos hn0 _
      have hpos3 : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hn0 _
      rw [div_le_iff₀ hpos]
      calc ‖f n‖ ≤ K * (n : ℝ) ^ ε := h2
        _ = K * (1 / (n : ℝ) ^ τ) * ((n : ℝ) ^ τ * (n : ℝ) ^ ε) := by field_simp
        _ ≤ K * (1 / (n : ℝ) ^ τ) * (n : ℝ) ^ s.re :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsumτ : Summable fun n : ℕ => ‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ :=
    (LSeriesSummable_one_iff.mpr (by simpa using hτ)).norm
  have hsum : Summable fun n : ℕ => ‖term f s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsumτ.mul_left K)
  calc ‖LSeries f s‖ = ‖∑' n : ℕ, term f s n‖ := rfl
    _ ≤ ∑' n : ℕ, ‖term f s n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, K * ‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ := hsum.tsum_le_tsum hterm (hsumτ.mul_left K)
    _ = K * ∑' n : ℕ, ‖term (1 : ℕ → ℂ) (τ : ℂ) n‖ := tsum_mul_left
    _ ≤ K * (τ / (τ - 1) + 1) := mul_le_mul_of_nonneg_left (tsum_norm_term_one_le hτ) hK

/-- `Λ(n) / log n ≤ 1`. -/
theorem norm_vonMangoldt_div_log_le (n : ℕ) : ‖(Λ n : ℂ) / (Real.log n : ℂ)‖ ≤ 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast h)
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg, abs_of_pos hl, div_le_one hl]
    exact vonMangoldt_le_log

/-- The Euler logarithm of `L(s, χ)` is bounded by `σ/(σ-1) + 1` on `re s = σ > 1`. -/
theorem norm_eulerLog_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n : ℕ => χ n * (Λ n : ℂ) / (Real.log n : ℂ)) s‖ ≤ s.re / (s.re - 1) + 1 := by
  have := norm_LSeries_le_zetaSum (f := fun n : ℕ => χ n * (Λ n : ℂ) / (Real.log n : ℂ))
    (K := 1) (ε := 0) (τ := s.re) (s := s) zero_le_one hs (by linarith) (fun n hn => by
      rw [Real.rpow_zero, mul_one, mul_div_assoc, norm_mul]
      calc ‖χ n‖ * ‖(Λ n : ℂ) / (Real.log n : ℂ)‖ ≤ 1 * 1 :=
            mul_le_mul (DirichletCharacter.norm_le_one χ n) (norm_vonMangoldt_div_log_le n)
              (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  simpa using this

/-- The Euler logarithm of `ζ`. -/
theorem norm_eulerLog_zeta_le {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n : ℕ => (Λ n : ℂ) / (Real.log n : ℂ)) s‖ ≤ s.re / (s.re - 1) + 1 := by
  have := norm_LSeries_le_zetaSum (f := fun n : ℕ => (Λ n : ℂ) / (Real.log n : ℂ))
    (K := 1) (ε := 0) (τ := s.re) (s := s) zero_le_one hs (by linarith) (fun n hn => by
      rw [Real.rpow_zero, mul_one]
      exact norm_vonMangoldt_div_log_le n)
  simpa using this

/-- The trivial bound for the series `∑ χ(n)Λ(n) n^{-s}` (the logarithmic derivative). -/
theorem norm_LSeries_twist_vonMangoldt_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    ‖LSeries (fun n : ℕ => χ n * (Λ n : ℂ)) s‖ ≤ 8 / (s.re - 1) ^ 2 := by
  set ε : ℝ := (s.re - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 / 2 := by rw [hε]; linarith
  have := norm_LSeries_le_zetaSum (f := fun n : ℕ => χ n * (Λ n : ℂ))
    (K := 1 / ε) (ε := ε) (τ := 1 + ε) (s := s) (by positivity) (by linarith)
    (by rw [hε]; linarith) (fun n hn => by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hlog : Real.log n ≤ (n : ℝ) ^ ε / ε := Real.log_le_rpow_div hn0 hε0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      calc ‖χ n‖ * Λ n ≤ 1 * Λ n :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ n) vonMangoldt_nonneg
        _ = Λ n := one_mul _
        _ ≤ Real.log n := vonMangoldt_le_log
        _ ≤ (n : ℝ) ^ ε / ε := hlog
        _ = 1 / ε * (n : ℝ) ^ ε := by ring)
  refine this.trans ?_
  have e : (1 + ε) / (1 + ε - 1) + 1 = (1 + 2 * ε) / ε := by
    have : 1 + ε - 1 = ε := by ring
    rw [this]; field_simp; ring
  rw [e]
  have h2 : (1 + 2 * ε) / ε ≤ 2 / ε := by
    rw [div_le_div_iff_of_pos_right hε0]; linarith
  have e2 : 8 / (s.re - 1) ^ 2 = 2 / ε ^ 2 := by
    rw [hε]; field_simp; ring
  rw [e2]
  calc 1 / ε * ((1 + 2 * ε) / ε) ≤ 1 / ε * (2 / ε) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 / ε ^ 2 := by field_simp

/-- `1 < log (q (|t| + 3))` for `q ≥ 1`. -/
theorem log_mul_abs_add_three_gt_one {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    1 < Real.log (q * (|t| + 3)) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h3 : (3 : ℝ) ≤ q * (|t| + 3) := by
    have := abs_nonneg t
    nlinarith
  have h4 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

end PrimeCarleson.Proof.Fplus31.PNTSW
