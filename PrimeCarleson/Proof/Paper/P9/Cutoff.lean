module

public import PrimeCarleson.Proof.Paper.P9.Carrier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The cutoffs `χ_I`, `φ_I` and the multiplier `η_I`

Source: main paper `s:MFanalysis`, L1861–L1871 (and the reproducing formula, L1872–L1876).

For a compact interval `I = [a, b] ⊂ 𝕋` in one coordinate chart `[θ, θ + 1]` of `𝕋`, and a length
`0 < c ≤ |I|/100`, the paper chooses Schwartz functions `χ_I, φ_I` with

* `1_{I + [-2c, 2c]} ≤ χ̂_I ≤ 1_{I + [-3c, 3c]}` (so `χ̂_I ≥ 0`), `φ_I(0) = 1`,
  `φ̂_I` vanishes off `[-c, c]`, `φ̂_I, φ_I ≥ 0`;

and `η_I := χ̂_I * φ̂_I`. **Choices left open**: the paper fixes neither the size of `φ_I` nor the
dilation of `χ_I`, although `∑_y φ_I(y)² ≲ |I|^{-1}` and `‖χ_I‖_{ℓ²} ≲ |I|^{1/2}` are used
(L1876–L1879, L2042–L2053). The choice made here:

* `CutoffData θ a b c` records `χ, φ : 𝓢(ℝ, ℂ)` with the printed properties and the size
  normalization `∫ |φ̂_I|² ≤ 2/c` (the form of "`φ̂_I` is a fixed profile dilated to scale `c`",
  `PhiData`-style data as for `K_Q`); `‖χ_I‖_{ℓ²} ≲ |I|^{1/2}` is *derived*
  (`Reproducing.lean`), no dilation is chosen for `χ_I`;
* the single chart condition is `θ < a - 4c`, `b + 4c < θ + 1` (the support of `η_I` is
  `I + [-4c, 4c]`);
* `φ_I` is real-valued (its Fourier transform is real, nonnegative and supported in `[-c, c]`);
  the printed positivity `φ_I ≥ 0` is not needed by any step and is not imposed: the hypotheses
  (A), (B) of `p:variable` only involve `|φ_I|`;
* `CutoffData.nonempty` (`CutoffExists.lean`): every `(θ, a, b, c)` with `0 < c`, `100 c ≤ b - a`
  and the chart condition carries such data, with `∫ |φ̂_I|² ≤ 1/c`.

`η_I = χ̂_I * φ̂_I` satisfies `η_I = 1` on `I + [-c, c]` (`eta_eq_one`), `η_I = 0` off
`I + [-4c, 4c]` (`eta_eq_zero`), and its inverse Fourier transform is `χ_I φ_I`
(`fourier_chiPhi`; the product of Schwartz functions is the Schwartz function `chiPhi`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-! ### Products of Schwartz functions and the Fourier transform of a product -/

/-- The product of two Schwartz functions as a Schwartz function. -/
def schwartzMul (F G : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (g := (G : ℝ → ℂ))
    G.hasTemperateGrowth F

@[simp] theorem schwartzMul_apply (F G : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzMul F G x = F x * G x := by
  simp [schwartzMul]

/-- **The Fourier transform of a product is the convolution of the transforms**:
`(F G)^(ζ) = ∫ F̂(ξ) Ĝ(ζ - ξ) dξ` for Schwartz `F, G`. -/
theorem fourier_schwartzMul (F G : 𝓢(ℝ, ℂ)) (ζ : ℝ) :
    𝓕 (⇑(schwartzMul F G)) ζ = ∫ ξ : ℝ, 𝓕 (⇑F) ξ * 𝓕 (⇑G) (ζ - ξ) := by
  have hF : ∀ x, F x = ∫ ξ, 𝓕 (⇑F) ξ * e (ξ * x) := fun x => fourier_inversion_schwartz F x
  have hFhat : Integrable (𝓕 (⇑F)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 F).integrable
  have hpt : ∀ x : ℝ, e (-(x * ζ)) * (schwartzMul F G x) =
      ∫ ξ, 𝓕 (⇑F) ξ * (G x * e (-(x * (ζ - ξ)))) := by
    intro x
    have hint : ∀ ξ : ℝ, 𝓕 (⇑F) ξ * (G x * e (-(x * (ζ - ξ)))) =
        (e (-(x * ζ)) * G x) * (𝓕 (⇑F) ξ * e (ξ * x)) := by
      intro ξ
      have : e (-(x * (ζ - ξ))) = e (-(x * ζ)) * e (ξ * x) := by
        rw [← e_add]; congr 1; ring
      rw [this]; ring
    simp_rw [hint, integral_const_mul]
    rw [schwartzMul_apply, hF x]
    ring
  rw [fourier_eq_integral_e]
  simp_rw [hpt]
  have hint : Integrable (Function.uncurry fun (x : ℝ) (ξ : ℝ) =>
      𝓕 (⇑F) ξ * (G x * e (-(x * (ζ - ξ))))) (volume.prod volume) := by
    refine Integrable.mono' (G.integrable.norm.mul_prod hFhat.norm) ?_ ?_
    · have hc1 : Continuous (𝓕 (⇑F)) := by
        rw [← SchwartzMap.fourier_coe]; exact (𝓕 F).continuous
      refine (hc1.comp continuous_snd).aestronglyMeasurable.mul
        ((G.continuous.comp continuous_fst).aestronglyMeasurable.mul
          (continuous_e.comp (by fun_prop)).aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun p => ?_
      change ‖𝓕 (⇑F) p.2 * (G p.1 * e (-(p.1 * (ζ - p.2))))‖ ≤ ‖G p.1‖ * ‖𝓕 (⇑F) p.2‖
      rw [norm_mul, norm_mul, norm_e, mul_one, mul_comm]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [integral_const_mul, fourier_eq_integral_e (⇑G) (ζ - ξ)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-! ### The cutoff data -/

/-- The cutoffs `χ_I, φ_I` (Source: main paper `s:MFanalysis`, L1861–L1871) for the interval
`I = [a, b]` in the chart `[θ, θ + 1]`, with the scale `c`, `0 < c ≤ |I|/100`; see the module
docstring for the choices made at the points the paper leaves open.
-/
structure CutoffData (θ a b c : ℝ) where
  /-- `χ_I`. -/
  χ : 𝓢(ℝ, ℂ)
  /-- `φ_I`. -/
  φ : 𝓢(ℝ, ℂ)
  /-- `c > 0`. -/
  c_pos : 0 < c
  /-- `c ≤ |I|/100`. -/
  c_le : 100 * c ≤ b - a
  /-- `I + [-4c, 4c]` lies in the chart `(θ, θ + 1)`: lower end. -/
  chart_lo : θ + 4 * c < a
  /-- `I + [-4c, 4c]` lies in the chart `(θ, θ + 1)`: upper end. -/
  chart_hi : b + 4 * c < θ + 1
  /-- `χ̂_I = 1` on `I + [-2c, 2c]`. -/
  chi_hat_one : ∀ ξ : ℝ, a - 2 * c ≤ ξ → ξ ≤ b + 2 * c → 𝓕 (⇑χ) ξ = 1
  /-- `χ̂_I = 0` off `I + [-3c, 3c]`. -/
  chi_hat_zero : ∀ ξ : ℝ, ξ ∉ Set.Icc (a - 3 * c) (b + 3 * c) → 𝓕 (⇑χ) ξ = 0
  /-- `0 ≤ χ̂_I ≤ 1`. -/
  chi_hat_mem : ∀ ξ : ℝ, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ 𝓕 (⇑χ) ξ = r
  /-- `φ_I(0) = 1`. -/
  phi_zero : φ 0 = 1
  /-- `φ_I` is real-valued. -/
  phi_real : ∀ x : ℝ, (φ x).im = 0
  /-- `φ̂_I ≥ 0`. -/
  phi_hat_nonneg : ∀ ξ : ℝ, ∃ r : ℝ, 0 ≤ r ∧ 𝓕 (⇑φ) ξ = r
  /-- `φ̂_I` vanishes off `[-c, c]`. -/
  phi_hat_zero : ∀ ξ : ℝ, c < |ξ| → 𝓕 (⇑φ) ξ = 0
  /-- The size normalization of `φ̂_I` (a profile dilated to scale `c`): `∫ |φ̂_I|² ≤ 2/c`. -/
  phi_scale : ∫ ξ : ℝ, ‖𝓕 (⇑φ) ξ‖ ^ 2 ≤ 2 / c

namespace CutoffData

variable {θ a b c : ℝ} (D : CutoffData θ a b c)

theorem chiHat_continuous : Continuous (𝓕 (⇑D.χ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 D.χ).continuous

theorem phiHat_continuous : Continuous (𝓕 (⇑D.φ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 D.φ).continuous

include D in
/-- `a ≤ b`. -/
theorem a_le_b : a ≤ b := by
  have := D.c_pos; have := D.c_le; linarith

/-- The multiplier `η_I := χ̂_I * φ̂_I` (L1866), `η_I(ζ) = ∫ χ̂_I(ξ) φ̂_I(ζ - ξ) dξ`. -/
def eta (ζ : ℝ) : ℂ := ∫ ξ : ℝ, 𝓕 (⇑D.χ) ξ * 𝓕 (⇑D.φ) (ζ - ξ)

/-- `∫ φ̂_I = φ_I(0) = 1`. -/
theorem integral_phiHat : ∫ ξ : ℝ, 𝓕 (⇑D.φ) ξ = 1 := by
  have h := fourier_inversion_schwartz D.φ 0
  simp only [mul_zero, e_zero, mul_one] at h
  rw [← h, D.phi_zero]

/-- **`η_I ≡ 1` on `I + [-c, c]`** (L1867). -/
theorem eta_eq_one {ζ : ℝ} (h1 : a - c ≤ ζ) (h2 : ζ ≤ b + c) : D.eta ζ = 1 := by
  have hc := D.c_pos
  unfold eta
  have hpt : ∀ ξ : ℝ, 𝓕 (⇑D.χ) ξ * 𝓕 (⇑D.φ) (ζ - ξ) = 𝓕 (⇑D.φ) (ζ - ξ) := by
    intro ξ
    by_cases hz : 𝓕 (⇑D.φ) (ζ - ξ) = 0
    · simp [hz]
    · have hle : |ζ - ξ| ≤ c := by
        by_contra hlt
        exact hz (D.phi_hat_zero _ (not_le.1 hlt))
      rw [abs_le] at hle
      rw [D.chi_hat_one ξ (by linarith) (by linarith), one_mul]
  simp_rw [hpt]
  rw [integral_sub_left_eq_self (fun ξ => 𝓕 (⇑D.φ) ξ) volume ζ]
  exact D.integral_phiHat

/-- `η_I` vanishes off `I + [-4c, 4c]` (the support of `χ̂_I` is `I + [-3c, 3c]`, that of `φ̂_I`
is `[-c, c]`). -/
theorem eta_eq_zero {ζ : ℝ} (h : ζ ∉ Set.Icc (a - 4 * c) (b + 4 * c)) : D.eta ζ = 0 := by
  unfold eta
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Pi.zero_apply]
  by_contra hne
  have h1 : 𝓕 (⇑D.χ) ξ ≠ 0 := left_ne_zero_of_mul hne
  have h2 : 𝓕 (⇑D.φ) (ζ - ξ) ≠ 0 := right_ne_zero_of_mul hne
  have hξ : ξ ∈ Set.Icc (a - 3 * c) (b + 3 * c) := by
    by_contra hnot; exact h1 (D.chi_hat_zero ξ hnot)
  have hle : |ζ - ξ| ≤ c := by
    by_contra hlt; exact h2 (D.phi_hat_zero _ (not_le.1 hlt))
  rw [abs_le] at hle
  apply h
  constructor <;> linarith [hξ.1, hξ.2, hle.1, hle.2]

/-- The Schwartz function `χ_I φ_I`. -/
def chiPhi : 𝓢(ℝ, ℂ) := schwartzMul D.χ D.φ

theorem chiPhi_apply (x : ℝ) : D.chiPhi x = D.χ x * D.φ x := schwartzMul_apply _ _ x

/-- **The Fourier transform of `χ_I φ_I` is `η_I = χ̂_I * φ̂_I`** (L1866-L1868). -/
theorem fourier_chiPhi (ζ : ℝ) : 𝓕 (⇑D.chiPhi) ζ = D.eta ζ :=
  fourier_schwartzMul D.χ D.φ ζ

end CutoffData

end PrimeCarleson.Proof.Paper
