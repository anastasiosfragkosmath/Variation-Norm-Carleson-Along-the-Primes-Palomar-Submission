module

public import PrimeCarleson.Proof.Paper.P9.Reproducing

/-!
# The sizes of `χ_I` and `φ_I`

Source: main paper `s:MFanalysis`, L1872–L1879 (`‖χ_I‖_{ℓ²} ≲ |I|^{1/2}`) and L2042–L2053
(`∑_y φ_I(y)² ≲ |I|^{-1}`), both by Parseval for the carrier (`hasSum_sq_invFZ`) after the carrier
change `restrict_eq_invFZ`.

* `sum_norm_sq_chi_le`: `‖χ_I‖²_{ℓ²(ℤ)} = ∫ |χ̂_I|² ≤ |I| + 6c`; with `c ≤ |I|/100`,
  `‖χ_I‖²_{ℓ²} ≤ (53/50) |I|`.
* `sum_norm_sq_phi_le`: `∑_y |φ_I(y)|² = ∫ |φ̂_I|² ≤ 2/c`; for `c ≥ |I|/200` this is
  `≤ 400 |I|^{-1}`.
* `phi_sq_series_eq_zero`: `∑_y |φ_I(y)|² e(τ y) = 0` if `2c < ‖τ‖_𝕋`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

namespace CutoffData

variable {θ a b c : ℝ} (D : CutoffData θ a b c)

/-- `|χ̂_I| ≤ 1`, supported in `I + [-3c, 3c]`: `|χ̂_I|² ≤ 1_{I + [-3c, 3c]}`. -/
theorem norm_chiHat_sq_le (ξ : ℝ) :
    ‖𝓕 (⇑D.χ) ξ‖ ^ 2 ≤ (Set.Icc (a - 3 * c) (b + 3 * c)).indicator (fun _ => (1 : ℝ)) ξ := by
  by_cases hξ : ξ ∈ Set.Icc (a - 3 * c) (b + 3 * c)
  · rw [Set.indicator_of_mem hξ]
    obtain ⟨r, hr0, hr1, hr⟩ := D.chi_hat_mem ξ
    rw [hr, Complex.norm_real, Real.norm_of_nonneg hr0]
    nlinarith
  · rw [Set.indicator_of_notMem hξ, D.chi_hat_zero ξ hξ]
    simp

/-- `∫_θ^{θ+1} |χ̂_I|² ≤ |I| + 6c`. -/
theorem integral_norm_chiHat_sq_le : ∫ β in θ..θ + 1, ‖𝓕 (⇑D.χ) β‖ ^ 2 ≤ b - a + 6 * c := by
  have hc := D.c_pos
  have hlo := D.chart_lo
  have hhi := D.chart_hi
  have hab := D.a_le_b
  have hsub : Set.Icc (a - 3 * c) (b + 3 * c) ⊆ Set.Ioc θ (θ + 1) := fun ξ hξ =>
    ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hcont : Continuous fun ξ => ‖𝓕 (⇑D.χ) ξ‖ ^ 2 := D.chiHat_continuous.norm.pow 2
  rw [intervalIntegral.integral_of_le (by linarith)]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub (fun ξ hξ => ?_)]
  · calc ∫ ξ in Set.Icc (a - 3 * c) (b + 3 * c), ‖𝓕 (⇑D.χ) ξ‖ ^ 2
        ≤ ∫ _ in Set.Icc (a - 3 * c) (b + 3 * c), (1 : ℝ) :=
          setIntegral_mono_on hcont.integrableOn_Icc (integrableOn_const (by simp))
            measurableSet_Icc fun ξ hξ => by
              simpa [Set.indicator_of_mem hξ] using D.norm_chiHat_sq_le ξ
      _ = b - a + 6 * c := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
          ring
  · have : ξ ∉ Set.Icc (a - 3 * c) (b + 3 * c) := hξ.2
    simp [D.chi_hat_zero ξ this]

/-- `χ_I|_ℤ` is the sequence with density `χ̂_I` on the chart. -/
theorem chi_eq_invFZ (n : ℤ) : D.χ n = invFZ θ (𝓕 (⇑D.χ)) n :=
  restrict_eq_invFZ D.χ (fun _ hξ => D.chiHat_eq_zero_of_not_mem hξ) n

/-- **Parseval for `χ_I`**: `∑_y |χ_I(y)|² = ∫_θ^{θ+1} |χ̂_I|²`. -/
theorem hasSum_norm_sq_chi :
    HasSum (fun y : ℤ => ‖D.χ y‖ ^ 2) (∫ β in θ..θ + 1, ‖𝓕 (⇑D.χ) β‖ ^ 2) := by
  have h := hasSum_sq_invFZ (θ := θ)
    (ChartL2.of_continuousOn D.chiHat_continuous.continuousOn)
  simpa only [← D.chi_eq_invFZ] using h

/-- **`‖χ_I‖²_{ℓ²(ℤ)} ≤ |I| + 6c`** (the printed `‖χ_I‖_{ℓ²} ≲ |I|^{1/2}`, L1876-L1879). -/
theorem sum_norm_sq_chi_le : ∑' y : ℤ, ‖D.χ y‖ ^ 2 ≤ b - a + 6 * c := by
  rw [D.hasSum_norm_sq_chi.tsum_eq]
  exact D.integral_norm_chiHat_sq_le

/-- `‖χ_I‖²_{ℓ²(ℤ)} ≤ (53/50) |I|`. -/
theorem sum_norm_sq_chi_le' : ∑' y : ℤ, ‖D.χ y‖ ^ 2 ≤ (53 / 50) * (b - a) := by
  have := D.sum_norm_sq_chi_le
  have := D.c_le
  linarith

/-- `φ_I|_ℤ` is the sequence with density `φ̂_I` on the chart `[-1/2, 1/2]`. -/
theorem phi_eq_invFZ (n : ℤ) : D.φ n = invFZ (-1 / 2) (𝓕 (⇑D.φ)) n := by
  refine restrict_eq_invFZ D.φ (fun ξ hξ => D.phi_hat_zero ξ ?_) n
  have := D.c_lt
  by_contra hle
  push Not at hle
  apply hξ
  rw [abs_le] at hle
  constructor <;> linarith [hle.1, hle.2]

/-- **Parseval for `φ_I`**: `∑_y |φ_I(y)|² = ∫ |φ̂_I|²`. -/
theorem hasSum_norm_sq_phi :
    HasSum (fun y : ℤ => ‖D.φ y‖ ^ 2)
      (∫ β in (-1 / 2 : ℝ)..(-1 / 2 : ℝ) + 1, ‖𝓕 (⇑D.φ) β‖ ^ 2) := by
  have h := hasSum_sq_invFZ (θ := -1 / 2)
    (ChartL2.of_continuousOn D.phiHat_continuous.continuousOn)
  simpa only [← D.phi_eq_invFZ] using h

/-- **The size of `φ_I`** (Source: main paper, L2042–L2053): `∑_y |φ_I(y)|² ≤ 2/c`. -/
theorem sum_norm_sq_phi_le : ∑' y : ℤ, ‖D.φ y‖ ^ 2 ≤ 2 / c := by
  rw [D.hasSum_norm_sq_phi.tsum_eq]
  refine le_trans (le_of_eq ?_) D.phi_scale
  have hc := D.c_lt
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_
  rw [D.phi_hat_zero ξ ?_]
  · simp
  · by_contra hle
    push Not at hle
    apply hξ
    rw [abs_le] at hle
    constructor <;> linarith [hle.1, hle.2]

/-- `|φ_I(y)|² = φ_I(y)²` as complex numbers, since `φ_I` is real. -/
theorem norm_phi_sq (y : ℝ) : ((‖D.φ y‖ ^ 2 : ℝ) : ℂ) = D.φ y * D.φ y := by
  have h : starRingEnd ℂ (D.φ y) = D.φ y := Complex.conj_eq_iff_im.2 (D.phi_real y)
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, h]

/-- **The Fourier series of `φ_I²` vanishes away from `ℤ`** (the Fourier transform of `φ_I²` is
the convolution `φ̂_I * φ̂_I`, supported in `[-2c, 2c]`, and Poisson summation applies):
`∑_y |φ_I(y)|² e(τ y) = 0` whenever `2c < |τ - v|` for all `v ∈ ℤ` (`2c < ‖τ‖_𝕋`). -/
theorem phi_sq_series_eq_zero {τ : ℝ} (hτ : ∀ v : ℤ, 2 * c < |τ - v|) :
    ∑' y : ℤ, ((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e (τ * y) = 0 := by
  have h := tsum_mul_e_eq_tsum_fourier_add_schwartz (schwartzMul D.φ D.φ) (-τ)
  simp_rw [schwartzMul_apply] at h
  have hL : ∀ y : ℤ, ((‖D.φ y‖ ^ 2 : ℝ) : ℂ) * e (τ * y) =
      D.φ y * D.φ y * e (-((y : ℝ) * (-τ))) := by
    intro y
    rw [D.norm_phi_sq]
    congr 2
    ring
  simp_rw [hL]
  rw [h]
  convert tsum_zero with v
  rw [fourier_schwartzMul]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Pi.zero_apply]
  by_contra hne
  have h1 : 𝓕 (⇑D.φ) ξ ≠ 0 := left_ne_zero_of_mul hne
  have h2 : 𝓕 (⇑D.φ) (-τ + v - ξ) ≠ 0 := right_ne_zero_of_mul hne
  have hξ : |ξ| ≤ c := by
    by_contra hlt; exact h1 (D.phi_hat_zero _ (not_le.1 hlt))
  have hξ' : |-τ + v - ξ| ≤ c := by
    by_contra hlt; exact h2 (D.phi_hat_zero _ (not_le.1 hlt))
  have := hτ v
  have h3 : |τ - v| ≤ |ξ| + |-τ + v - ξ| := by
    calc |τ - v| = |-(-τ + v - ξ) - ξ| := by congr 1; ring
      _ ≤ |-(-τ + v - ξ)| + |ξ| := abs_sub _ _
      _ = |ξ| + |-τ + v - ξ| := by rw [abs_neg]; ring
  linarith

end CutoffData

end PrimeCarleson.Proof.Paper
