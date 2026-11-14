module

public import PrimeCarleson.Proof.Paper.P9.Cutoff
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Existence of the cutoff data `χ_I, φ_I`

Source: main paper `s:MFanalysis`, L1861–L1871.
`CutoffData.nonempty`: for `0 < c`, `100 c ≤ b - a` and `I + [-4c, 4c]` in the chart `(θ, θ + 1)`
there is `CutoffData θ a b c`: `χ̂_I` and `φ̂_I` are smooth bumps (as for `PhiData.nonempty`),
`χ_I = 𝓕⁻ χ̂_I`, `φ_I = 𝓕⁻ φ̂_I`; the profile of `φ̂_I` is `N⁻¹` times a bump of radii
`c/2, c` (`N` the integral of the bump), which has integral `1`, so `φ_I(0) = 1`, and
`∫ |φ̂_I|² ≤ 1/c ≤ 2/c`. `φ_I` is real-valued because `φ̂_I` is real and even.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- A real smooth compactly supported function is (the real part of) a Schwartz function. -/
theorem exists_schwartz_ofReal {f : ℝ → ℝ} (hc : HasCompactSupport f) (hd : ContDiff ℝ ∞ f) :
    ∃ S : 𝓢(ℝ, ℂ), ∀ x, S x = ((f x : ℝ) : ℂ) := by
  have hc' : HasCompactSupport (fun x : ℝ => ((f x : ℝ) : ℂ)) :=
    hc.comp_left Complex.ofReal_zero
  have hd' : ContDiff ℝ ∞ (fun x : ℝ => ((f x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hd
  exact ⟨hc'.toSchwartzMap hd', fun _ => rfl⟩

/-- `𝓕 (𝓕⁻ S) = S` on the level of functions. -/
theorem fourier_fourierInv_apply (S : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (⇑(𝓕⁻ S : 𝓢(ℝ, ℂ))) ξ = S ξ := by
  rw [← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq]

/-- **Existence of the cutoffs** (Source: main paper `s:MFanalysis`, L1861–L1871): for `0 < c`,
`100 c ≤ |I|` and `I + [-4c, 4c]` in the chart `(θ, θ + 1)`, `CutoffData θ a b c` is inhabited. -/
theorem CutoffData.nonempty {θ a b c : ℝ} (hc : 0 < c) (hcl : 100 * c ≤ b - a)
    (h1 : θ + 4 * c < a) (h2 : b + 4 * c < θ + 1) : Nonempty (CutoffData θ a b c) := by
  -- the bump for `χ̂`
  let m : ℝ := (a + b) / 2
  let bump1 : ContDiffBump m :=
    ⟨(b - a) / 2 + 2 * c, (b - a) / 2 + 3 * c, by linarith, by linarith⟩
  obtain ⟨S1, hS1⟩ := exists_schwartz_ofReal (f := fun x => bump1 x)
    bump1.hasCompactSupport bump1.contDiff
  -- the bump for `φ̂`
  let bump2 : ContDiffBump (0 : ℝ) := ⟨c / 2, c, by linarith, by linarith⟩
  let N : ℝ := ∫ x, bump2 x
  have hN1 : c ≤ N := by
    have := bump2.measure_closedBall_le_integral volume
    have h0 : volume.real (Metric.closedBall (0 : ℝ) bump2.rIn) = c := by
      rw [Real.volume_real_closedBall bump2.rIn_pos.le]
      change 2 * (c / 2) = c
      ring
    linarith
  have hNpos : 0 < N := hc.trans_le hN1
  obtain ⟨S2, hS2⟩ := exists_schwartz_ofReal (f := fun x => N⁻¹ * bump2 x)
    (bump2.hasCompactSupport.mul_left) (contDiff_const.mul bump2.contDiff)
  have hb2int : Integrable (fun x : ℝ => (bump2 x : ℝ)) :=
    bump2.continuous.integrable_of_hasCompactSupport bump2.hasCompactSupport
  -- the cutoffs
  refine ⟨⟨(𝓕⁻ S1 : 𝓢(ℝ, ℂ)), (𝓕⁻ S2 : 𝓢(ℝ, ℂ)), hc, hcl, h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro ξ hξ1 hξ2
    rw [fourier_fourierInv_apply, hS1, bump1.one_of_mem_closedBall]
    · simp
    · rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> simp only [m, bump1] <;> linarith
  · intro ξ hξ
    rw [fourier_fourierInv_apply, hS1, bump1.zero_of_le_dist]
    · simp
    · rw [Real.dist_eq]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hξ
      change (b - a) / 2 + 3 * c ≤ |ξ - m|
      rcases hξ with h | h
      · rw [abs_of_neg (by simp only [m]; linarith)]; simp only [m]; linarith
      · rw [abs_of_pos (by simp only [m]; linarith)]; simp only [m]; linarith
  · intro ξ
    refine ⟨bump1 ξ, bump1.nonneg, bump1.le_one, ?_⟩
    rw [fourier_fourierInv_apply, hS1]
  · -- `φ 0 = 1`
    have h := fourier_inversion_schwartz (𝓕⁻ S2 : 𝓢(ℝ, ℂ)) 0
    simp only [mul_zero, e_zero, mul_one] at h
    rw [h]
    simp_rw [fourier_fourierInv_apply, hS2]
    rw [integral_complex_ofReal, integral_const_mul]
    have : N⁻¹ * N = 1 := inv_mul_cancel₀ hNpos.ne'
    rw [show (∫ x, (bump2 x : ℝ)) = N from rfl, this]; simp
  · -- `φ` real
    intro x
    have hev : ∀ ξ : ℝ, S2 (-ξ) = S2 ξ := by
      intro ξ; rw [hS2, hS2, bump2.neg]
    have hreal : ∀ ξ : ℝ, (starRingEnd ℂ) (S2 ξ) = S2 ξ := by
      intro ξ; rw [hS2]; exact Complex.conj_ofReal _
    have hconj : (starRingEnd ℂ) ((𝓕⁻ S2 : 𝓢(ℝ, ℂ)) x) = (𝓕⁻ S2 : 𝓢(ℝ, ℂ)) x := by
      rw [SchwartzMap.fourierInv_coe, fourierInv_eq_integral_e, ← integral_conj]
      conv_rhs => rw [← integral_neg_eq_self (fun ξ => e (ξ * x) * S2 ξ) volume]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [map_mul, ← e_neg, hreal, hev]
      congr 2
      ring
    exact Complex.conj_eq_iff_im.1 hconj
  · intro ξ
    refine ⟨N⁻¹ * bump2 ξ, mul_nonneg (inv_nonneg.2 hNpos.le) bump2.nonneg, ?_⟩
    rw [fourier_fourierInv_apply, hS2]
  · intro ξ hξ
    rw [fourier_fourierInv_apply, hS2, bump2.zero_of_le_dist]
    · simp
    · rw [Real.dist_eq]; simp only [sub_zero]; exact hξ.le
  · have hpt : ∀ ξ : ℝ, ‖𝓕 (⇑(𝓕⁻ S2 : 𝓢(ℝ, ℂ))) ξ‖ ^ 2 ≤ N⁻¹ ^ 2 * bump2 ξ := by
      intro ξ
      rw [fourier_fourierInv_apply, hS2, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hNpos.le) bump2.nonneg), mul_pow]
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [bump2.nonneg (x := ξ), bump2.le_one (x := ξ)]) (by positivity)
    calc ∫ ξ : ℝ, ‖𝓕 (⇑(𝓕⁻ S2 : 𝓢(ℝ, ℂ))) ξ‖ ^ 2 ≤ ∫ ξ : ℝ, N⁻¹ ^ 2 * bump2 ξ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity)
            (hb2int.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = N⁻¹ ^ 2 * N := by rw [integral_const_mul]
      _ = N⁻¹ := by field_simp
      _ ≤ c⁻¹ := inv_anti₀ hc hN1
      _ ≤ 2 / c := by
          rw [div_eq_mul_inv]
          have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
          linarith

end PrimeCarleson.Proof.Paper
