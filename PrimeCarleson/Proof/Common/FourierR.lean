module

public import PrimeCarleson.Proof.Common.FourierZ
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fourier analysis on `ℝ` used as folklore by the paper

Mathlib's Fourier transform `𝓕 f ξ = ∫ x, 𝐞 (-(x ξ)) • f x` (`𝐞 t = exp (2πit)`) is the
convention of `sources/Variational_Carleson.tex`, namely `f̂(ξ) = ∫ f(x) e(-xξ) dx` with
`PrimeCarleson.e t = exp (2πit)`. The first block restates it with `PrimeCarleson.e`
(`fourier_eq_integral_e`, `fourierInv_eq_integral_e`). The other blocks prove three standard
facts that the paper uses without proof.

* The `L¹` bound for the Fourier transform of a `C²` function (used at L874, in the proof of
  `e:U3maxmod`, where `φ ∈ C_c²([0,1])` and `‖φ̂‖_{L¹} ≲ ‖φ‖_{C²}`; the paper does not define
  `‖·‖_{C²}`):
  `integrable_fourier_of_contDiff_two` (`φ̂` is integrable for `φ ∈ C_c²`),
  `norm_fourier_le_of_contDiff_two` (the decay `|φ̂(ξ)| ≲ (1 + ξ²)⁻¹`),
  `integral_norm_fourier_le` (explicit constants for support in `[a, b]`),
  `integral_norm_fourier_le_four_mul` (`‖φ̂‖_{L¹} ≤ 4 M` if `sup |φ|, sup |φ''| ≤ M`).
* Fourier inversion (used at L886, in the proof of `e:U3maxmod`, at L1872-L1879, and in the
  arguments of [MSW] and [O+] that invert a compactly supported smooth `Φ̂`):
  `fourier_inversion_of_contDiff_two`
  (`φ(t) = ∫ φ̂(ξ) e(ξt) dξ` for `φ ∈ C_c²`), its dilate `fourier_inversion_div`
  (`φ(t / N)`), and the Schwartz version `fourier_inversion_schwartz`.
* Poisson summation (used at L2966, in the proof of `p:disc`, and in the passage from `ℝ` to `ℤ`
  for the cutoffs `χ_I`, `φ_I`, L1861-L1879): `tsum_mul_e_eq_tsum_fourier_add`
  (`∑_n h(n) e(-nβ) = ∑_v ĥ(β + v)` for `h` continuous with `h`, `ĥ = O(|x|^{-b})`, `b > 1`),
  specialised to `C_c²` (`tsum_mul_e_eq_tsum_fourier_add_of_contDiff_two`) and Schwartz
  functions (`tsum_mul_e_eq_tsum_fourier_add_schwartz`), with summability of both sides.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform Real SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### The Fourier transform in terms of `PrimeCarleson.e` -/

/-- `e t` is Mathlib's `𝐞 t = exp (2πit)`. -/
theorem e_eq_coe_fourierChar (t : ℝ) : e t = ((Real.fourierChar t : Circle) : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold e
  congr 1
  push_cast
  ring

/-- `f̂(ξ) = ∫ f(x) e(-xξ) dx`: Mathlib's `𝓕` in the notation of the paper. -/
theorem fourier_eq_integral_e (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x : ℝ, e (-(x * ξ)) * f x := by
  rw [Real.fourier_real_eq]
  simp only [Circle.smul_def, e_eq_coe_fourierChar, smul_eq_mul]

/-- The inverse Fourier transform `𝓕⁻ f (t) = ∫ f(ξ) e(ξt) dξ`. -/
theorem fourierInv_eq_integral_e (f : ℝ → ℂ) (t : ℝ) :
    𝓕⁻ f t = ∫ ξ : ℝ, e (ξ * t) * f ξ := by
  rw [Real.fourierInv_eq]
  simp only [Circle.smul_def, e_eq_coe_fourierChar, RCLike.inner_apply, conj_trivial,
    smul_eq_mul]
  congr 1
  ext ξ
  rw [mul_comm t ξ]

/-- The second iterated derivative is `deriv (deriv φ)`. -/
theorem iteratedDeriv_two_eq_deriv_deriv (φ : ℝ → ℂ) : iteratedDeriv 2 φ = deriv (deriv φ) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-! ### `L¹` bound for the Fourier transform of a `C²` function -/

/-- The iterated derivatives of a compactly supported function are compactly supported. -/
theorem hasCompactSupport_iteratedDeriv {φ : ℝ → ℂ} (hc : HasCompactSupport φ) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n φ) := by
  induction n with
  | zero => simpa using hc
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- The derivatives up to order two of a compactly supported `C²` function are integrable. -/
theorem integrable_iteratedDeriv_of_contDiff_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) {k : ℕ} (hk : k ≤ 2) : Integrable (iteratedDeriv k φ) :=
  (hφ.continuous_iteratedDeriv k (by exact_mod_cast hk)).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv hc k)

/-- Quadratic decay of the Fourier transform of a compactly supported `C²` function:
`(1 + ξ²) |φ̂(ξ)| ≤ ‖φ‖_{L¹} + (4π²)⁻¹ ‖φ''‖_{L¹}`. -/
theorem norm_fourier_le_of_contDiff_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (u : ℝ) :
    ‖𝓕 φ u‖ ≤ ((∫ v, ‖φ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv φ) v‖) / (1 + u ^ 2) := by
  have h := Real.one_add_sq_mul_norm_fourier_le hφ
    (fun k hk => integrable_iteratedDeriv_of_contDiff_two hφ hc hk) u
  rw [iteratedDeriv_two_eq_deriv_deriv] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The Fourier transform of an integrable function is continuous. -/
theorem continuous_fourier_of_integrable {φ : ℝ → ℂ} (hφ : Integrable φ) : Continuous (𝓕 φ) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simp only [innerₗ_apply_apply]; exact continuous_inner) hφ

/-- **Integrability of `φ̂`** for `φ ∈ C_c²(ℝ)`. -/
theorem integrable_fourier_of_contDiff_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) : Integrable (𝓕 φ) := by
  have hint : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul
    ((∫ v, ‖φ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv φ) v‖))
    (continuous_fourier_of_integrable hint).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [← div_eq_mul_inv]
  exact norm_fourier_le_of_contDiff_two hφ hc u

/-- `‖φ̂‖_{L¹} ≤ π (‖φ‖_{L¹} + (4π²)⁻¹ ‖φ''‖_{L¹})` for `φ ∈ C_c²(ℝ)`. -/
theorem integral_norm_fourier_le_of_contDiff_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) :
    ∫ ξ, ‖𝓕 φ ξ‖ ≤ π * ((∫ v, ‖φ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv φ) v‖) := by
  have hF := integrable_fourier_of_contDiff_two hφ hc
  have hB := (integrable_inv_one_add_sq.const_mul
    ((∫ v, ‖φ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv φ) v‖))
  calc ∫ ξ, ‖𝓕 φ ξ‖
      ≤ ∫ ξ : ℝ, ((∫ v, ‖φ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv φ) v‖) *
          (1 + ξ ^ 2)⁻¹ := by
        refine integral_mono hF.norm hB fun u => ?_
        rw [← div_eq_mul_inv]
        exact norm_fourier_le_of_contDiff_two hφ hc u
    _ = _ := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq, mul_comm]

/-- A function vanishing outside `[a, b]` and bounded by `C` has `L¹` norm at most `(b - a) C`. -/
theorem integral_norm_le_of_support_subset_Icc {f : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hs : Function.support f ⊆ Set.Icc a b) (hC : ∀ t, ‖f t‖ ≤ C) :
    ∫ t, ‖f t‖ ≤ (b - a) * C := by
  have hint : Integrable (Set.indicator (Set.Icc a b) fun _ : ℝ => C) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  calc ∫ t, ‖f t‖ ≤ ∫ t, Set.indicator (Set.Icc a b) (fun _ : ℝ => C) t := by
        refine integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) hint
          (ae_of_all _ fun t => ?_)
        by_cases ht : t ∈ Set.Icc a b
        · rw [Set.indicator_of_mem ht]; exact hC t
        · rw [Set.indicator_of_notMem ht]
          have : f t = 0 := by
            by_contra h
            exact ht (hs h)
          simp [this]
    _ = (b - a) * C := by
        rw [integral_indicator_const _ measurableSet_Icc]
        simp [Real.volume_real_Icc, hab, smul_eq_mul]

/-- `‖φ̂‖_{L¹} ≤ π (b - a) A₀ + (b - a) A₂ / (4π)` for `φ ∈ C²` supported in `[a, b]` (that is,
`support φ ⊆ [a, b]`) with `|φ| ≤ A₀` and `|φ''| ≤ A₂`. -/
theorem integral_norm_fourier_le {φ : ℝ → ℂ} {a b A₀ A₂ : ℝ} (hab : a ≤ b)
    (hφ : ContDiff ℝ 2 φ) (hsupp : Function.support φ ⊆ Set.Icc a b)
    (h0 : ∀ t, ‖φ t‖ ≤ A₀) (h2 : ∀ t, ‖deriv (deriv φ) t‖ ≤ A₂) :
    ∫ ξ, ‖𝓕 φ ξ‖ ≤ π * ((b - a) * A₀) + (b - a) * A₂ / (4 * π) := by
  have hts : tsupport φ ⊆ Set.Icc a b := closure_minimal hsupp isClosed_Icc
  have hc : HasCompactSupport φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ) hts
  have h1 := integral_norm_fourier_le_of_contDiff_two hφ hc
  have hX : ∫ v, ‖φ v‖ ≤ (b - a) * A₀ :=
    integral_norm_le_of_support_subset_Icc hab hsupp h0
  have hY : ∫ v, ‖deriv (deriv φ) v‖ ≤ (b - a) * A₂ :=
    integral_norm_le_of_support_subset_Icc hab
      ((support_deriv_subset.trans tsupport_deriv_subset).trans hts) h2
  have hπ : 0 < π := Real.pi_pos
  calc ∫ ξ, ‖𝓕 φ ξ‖
      ≤ π * ((∫ v, ‖φ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv φ) v‖) := h1
    _ ≤ π * ((b - a) * A₀ + (4 * π ^ 2)⁻¹ * ((b - a) * A₂)) := by
        gcongr
    _ = _ := by field_simp

/-- **`‖φ̂‖_{L¹(ℝ)} ≤ 4 ‖φ‖_{C²}`**: for `φ ∈ C²(ℝ)`
supported in `[0, 1]` with `|φ|, |φ''| ≤ M` (so in particular whenever `M` bounds the `C²` norm,
whether it is defined as a sum or as a maximum of `sup |φ|`, `sup |φ'|`, `sup |φ''|`),
`∫ |φ̂| ≤ 4 M`. -/
theorem integral_norm_fourier_le_four_mul {φ : ℝ → ℂ} {M : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) (h0 : ∀ t, ‖φ t‖ ≤ M)
    (h2 : ∀ t, ‖deriv (deriv φ) t‖ ≤ M) : ∫ ξ, ‖𝓕 φ ξ‖ ≤ 4 * M := by
  have h := integral_norm_fourier_le zero_le_one hφ hsupp h0 h2
  have hM : 0 ≤ M := (norm_nonneg _).trans (h0 0)
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have h5 : (1 - 0 : ℝ) * M / (4 * π) ≤ M / 12 := by
    rw [sub_zero, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h6 : π * ((1 - 0 : ℝ) * M) ≤ 3.15 * M := by
    rw [sub_zero, one_mul]
    exact mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hM
  linarith

/-- A continuous compactly supported function has bounded norm. -/
theorem bddAbove_range_norm_of_hasCompactSupport {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : BddAbove (Set.range fun t => ‖f t‖) :=
  hf.norm.bddAbove_range_of_hasCompactSupport hc.norm

/-! ### Fourier inversion -/

/-- **Fourier inversion**: `φ(t) = ∫ φ̂(ξ) e(ξt) dξ` for continuous integrable `φ` with
integrable `φ̂`. -/
theorem fourier_inversion_of_integrable {φ : ℝ → ℂ} (hc : Continuous φ) (hφ : Integrable φ)
    (hF : Integrable (𝓕 φ)) (t : ℝ) : φ t = ∫ ξ : ℝ, 𝓕 φ ξ * e (ξ * t) := by
  have h := congrFun (hc.fourierInv_fourier_eq hφ hF) t
  rw [← h, fourierInv_eq_integral_e]
  simp_rw [mul_comm (e _)]

/-- **Fourier inversion for `φ ∈ C_c²(ℝ)`**: `φ̂` is integrable
and `φ(t) = ∫ φ̂(ξ) e(ξt) dξ` for every real `t`. -/
theorem fourier_inversion_of_contDiff_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (t : ℝ) : φ t = ∫ ξ : ℝ, 𝓕 φ ξ * e (ξ * t) :=
  fourier_inversion_of_integrable hφ.continuous (hφ.continuous.integrable_of_hasCompactSupport hc)
    (integrable_fourier_of_contDiff_two hφ hc) t

/-- Fourier inversion at the dilated point `t / N` (as used for `φ(n / N)`):
`φ(t / N) = ∫ φ̂(ξ) e(ξ t / N) dξ`. -/
theorem fourier_inversion_div {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (t N : ℝ) : φ (t / N) = ∫ ξ : ℝ, 𝓕 φ ξ * e (ξ * t / N) := by
  rw [fourier_inversion_of_contDiff_two hφ hc (t / N)]
  simp_rw [mul_div_assoc]

/-- Fourier inversion for a Schwartz function. -/
theorem fourier_inversion_schwartz (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    f t = ∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ * e (ξ * t) :=
  fourier_inversion_of_integrable f.continuous f.integrable (𝓕 f).integrable t

/-! ### Poisson summation -/

/-- Modulation by `e(-βx)` translates the Fourier transform: `(h e(-β ·))^ (ξ) = ĥ(ξ + β)`. -/
theorem fourier_mul_e_neg (h : ℝ → ℂ) (β ξ : ℝ) :
    𝓕 (fun x : ℝ => h x * e (-(x * β))) ξ = 𝓕 h (ξ + β) := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e]
  congr 1
  ext x
  have : -(x * (ξ + β)) = -(x * ξ) + -(x * β) := by ring
  rw [this, e_add]
  ring

open Filter Asymptotics in
/-- If `ĥ = O(|x|^{-b})` at infinity with `b > 1`, then `∑_v ĥ(β + v)` converges absolutely. -/
theorem summable_fourier_add_int {h : ℝ → ℂ} {b : ℝ} (hb : 1 < b)
    (hF : 𝓕 h =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b)) (β : ℝ) :
    Summable fun v : ℤ => 𝓕 h (β + v) := by
  have hT : Tendsto (fun v : ℤ => β + (v : ℝ)) cofinite (cocompact ℝ) :=
    (Homeomorph.addLeft β).isClosedEmbedding.tendsto_cocompact.comp Int.tendsto_coe_cofinite
  refine summable_of_isBigO ((Real.summable_one_div_int_add_rpow β b).2 hb) ?_
  refine (hF.comp_tendsto hT).congr_right fun v => ?_
  simp only [Function.comp_apply, one_div, add_comm β]
  rw [Real.rpow_neg (abs_nonneg _)]

open Filter Asymptotics in
/-- Modulation by `e(-βx)` preserves decay at infinity. -/
theorem isBigO_mul_e_neg {h : ℝ → ℂ} {b : ℝ}
    (hh : h =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b)) (β : ℝ) :
    (fun x : ℝ => h x * e (-(x * β))) =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b) := by
  obtain ⟨C, hC⟩ := hh.bound
  refine IsBigO.of_bound C (hC.mono fun x hx => ?_)
  simpa [norm_mul, norm_e] using hx

open Filter Asymptotics in
/-- If `h = O(|x|^{-b})` at infinity with `b > 1`, then `∑_n h(n) e(-nβ)` converges absolutely. -/
theorem summable_mul_e_int {h : ℝ → ℂ} {b : ℝ} (hb : 1 < b)
    (hh : h =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b)) (β : ℝ) :
    Summable fun n : ℤ => h n * e (-((n : ℝ) * β)) :=
  summable_of_isBigO (Real.summable_abs_int_rpow hb)
    ((isBigO_mul_e_neg hh β).comp_tendsto Int.tendsto_coe_cofinite)

open Filter Asymptotics in
/-- **Poisson summation**, `∑_{n ∈ ℤ} h(n) e(-βn) = ∑_{v ∈ ℤ} ĥ(β + v)`, for a continuous `h`
such that `h` and `ĥ` are `O(|x|^{-b})` at infinity for some `b > 1`. Both sides converge
absolutely (`summable_mul_e_int`, `summable_fourier_add_int`). -/
theorem tsum_mul_e_eq_tsum_fourier_add {h : ℝ → ℂ} (hc : Continuous h) {b : ℝ} (hb : 1 < b)
    (hh : h =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b))
    (hF : 𝓕 h =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b)) (β : ℝ) :
    ∑' n : ℤ, h n * e (-((n : ℝ) * β)) = ∑' v : ℤ, 𝓕 h (β + v) := by
  have hfc : Continuous fun x : ℝ => h x * e (-(x * β)) :=
    hc.mul (continuous_e.comp (by fun_prop))
  have hS : Summable fun n : ℤ => 𝓕 (fun x : ℝ => h x * e (-(x * β))) n := by
    simp_rw [fourier_mul_e_neg, add_comm _ β]
    exact summable_fourier_add_int hb hF β
  have := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hfc hb (isBigO_mul_e_neg hh β) hS 0
  simpa [fourier_mul_e_neg, add_comm _ β] using this

open Filter Asymptotics in
/-- A compactly supported function is `O(g)` at infinity for every `g`. -/
theorem isBigO_cocompact_of_hasCompactSupport {h : ℝ → ℂ} (hc : HasCompactSupport h)
    (g : ℝ → ℝ) : h =O[cocompact ℝ] g := by
  have h0 : h =ᶠ[cocompact ℝ] 0 := by
    simpa [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] using hc
  exact h0.trans_isBigO (isBigO_zero _ _)

open Filter Asymptotics in
/-- The Fourier transform of a compactly supported `C²` function is `O(|ξ|^{-2})`. -/
theorem isBigO_fourier_of_contDiff_two {h : ℝ → ℂ} (hφ : ContDiff ℝ 2 h)
    (hc : HasCompactSupport h) :
    𝓕 h =O[cocompact ℝ] fun x : ℝ => |x| ^ (-(2 : ℝ)) := by
  refine IsBigO.of_bound ((∫ v, ‖h v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv h) v‖) ?_
  filter_upwards [Filter.cocompact_le_cofinite (eventually_cofinite_ne (0 : ℝ))] with u hu
  have h1 := norm_fourier_le_of_contDiff_two hφ hc u
  have hu2 : 0 < u ^ 2 := by positivity
  have h2 : |u| ^ (-(2 : ℝ)) = (u ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs]
  rw [Real.norm_eq_abs, h2, abs_of_pos (inv_pos.2 hu2)]
  refine h1.trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ hu2 (by linarith)

/-- **Poisson summation for `h ∈ C_c²(ℝ)`**: `∑_{n ∈ ℤ} h(n) e(-βn) = ∑_{v ∈ ℤ} ĥ(β + v)`. -/
theorem tsum_mul_e_eq_tsum_fourier_add_of_contDiff_two {h : ℝ → ℂ} (hφ : ContDiff ℝ 2 h)
    (hc : HasCompactSupport h) (β : ℝ) :
    ∑' n : ℤ, h n * e (-((n : ℝ) * β)) = ∑' v : ℤ, 𝓕 h (β + v) :=
  tsum_mul_e_eq_tsum_fourier_add hφ.continuous one_lt_two
    (isBigO_cocompact_of_hasCompactSupport hc _) (isBigO_fourier_of_contDiff_two hφ hc) β

/-- **Poisson summation for a Schwartz function**:
`∑_{n ∈ ℤ} h(n) e(-βn) = ∑_{v ∈ ℤ} ĥ(β + v)`. -/
theorem tsum_mul_e_eq_tsum_fourier_add_schwartz (h : 𝓢(ℝ, ℂ)) (β : ℝ) :
    ∑' n : ℤ, h n * e (-((n : ℝ) * β)) = ∑' v : ℤ, 𝓕 (h : ℝ → ℂ) (β + v) :=
  tsum_mul_e_eq_tsum_fourier_add h.continuous one_lt_two (h.isBigO_cocompact_rpow (-2))
    ((𝓕 h).isBigO_cocompact_rpow (-2)) β

/-- The right side of Poisson summation converges absolutely for `h ∈ C_c²(ℝ)`. -/
theorem summable_fourier_add_int_of_contDiff_two {h : ℝ → ℂ} (hφ : ContDiff ℝ 2 h)
    (hc : HasCompactSupport h) (β : ℝ) : Summable fun v : ℤ => 𝓕 h (β + v) :=
  summable_fourier_add_int one_lt_two (isBigO_fourier_of_contDiff_two hφ hc) β

/-- The left side of Poisson summation converges absolutely for a Schwartz function. -/
theorem summable_mul_e_int_schwartz (h : 𝓢(ℝ, ℂ)) (β : ℝ) :
    Summable fun n : ℤ => h n * e (-((n : ℝ) * β)) :=
  summable_mul_e_int one_lt_two (h.isBigO_cocompact_rpow (-2)) β

end PrimeCarleson.Proof.Common
