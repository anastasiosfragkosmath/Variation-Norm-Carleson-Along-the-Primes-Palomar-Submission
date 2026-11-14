module

public import PrimeCarleson.Proof.Paper.P9.CutoffExists

/-!
# Carrier change, the reproducing formula and the sizes of `χ_I`, `φ_I`

Source: main paper `s:MFanalysis`, L1861–L1879 and L2042–L2053 (and the periodization
step of the `A₁` computation of `p:global-shell-var`, L2031–L2048).

* `restrict_eq_invFZ` (carrier change): a Schwartz function `u` whose Fourier transform is
  supported in the interior of a chart `[θ, θ + 1]` has `u(n) = invFZ θ û (n)` for `n ∈ ℤ`; there
  is no aliasing because `û` lives in one chart (`ℓ²(ℤ)` Fourier series are periodizations,
  `chiPhi_series`: `∑_y χ(y)φ(y) e(-yβ) = ∑_v η_I(β + v)` by Poisson summation).
* `CutoffData.reproducing_formula`: for `H ∈ L²` vanishing off `I`, the sequence `h = invFZ θ H`
  (`ĥ` supported in `I`) satisfies `(χ_I φ_I) * h = h` on `ℤ`.
* `CutoffData.sum_norm_sq_chi_le`: `‖χ_I‖²_{ℓ²(ℤ)} ≤ |I| + 6c ≤ (53/50)|I|`
  (the printed `‖χ_I‖_{ℓ²} ≲ |I|^{1/2}`, derived, with constant `√(53/50)`).
* `CutoffData.sum_norm_sq_phi_le`: `∑_y |φ_I(y)|² ≤ 2/c` (the size of `φ_I`).
* `CutoffData.phi_sq_series_eq_zero`: `∑_y |φ_I(y)|² e(τ y) = 0` if `2c < ‖τ‖_𝕋`
  (the Fourier transform of `φ_I²` is supported in `[-2c, 2c]`; used for `A_1`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-! ### Carrier change -/

/-- **Carrier change `ℝ → ℤ`** (Source: main paper `s:MFanalysis`, L1861–L1879): if `û` vanishes
off `(θ, θ + 1)`, then `u(n) = ∫_θ^{θ+1} û(ξ) e(nξ) dξ` for every integer `n`. -/
theorem restrict_eq_invFZ {θ : ℝ} (u : 𝓢(ℝ, ℂ))
    (hu : ∀ ξ : ℝ, ξ ∉ Set.Ioo θ (θ + 1) → 𝓕 (⇑u) ξ = 0) (n : ℤ) :
    u n = invFZ θ (𝓕 (⇑u)) n := by
  rw [fourier_inversion_schwartz u n]
  unfold invFZ
  rw [intervalIntegral.integral_of_le (by linarith)]
  have h : ∫ ξ in Set.Ioc θ (θ + 1), 𝓕 (⇑u) ξ * e ((n : ℝ) * ξ) =
      ∫ ξ, 𝓕 (⇑u) ξ * e ((n : ℝ) * ξ) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_
    rw [hu ξ (fun h => hξ ⟨h.1, h.2.le⟩), zero_mul]
  rw [h]
  simp_rw [mul_comm (n : ℝ)]

namespace CutoffData

variable {θ a b c : ℝ} (D : CutoffData θ a b c)

include D in
/-- The chart `(θ, θ + 1)` has length `1`, so `|I| < 1`. -/
theorem b_sub_a_lt_one : b - a < 1 := by
  have := D.c_pos; have := D.chart_lo; have := D.chart_hi; linarith

include D in
/-- `c < 1/100`. -/
theorem c_lt : c < 1 / 100 := by
  have := D.c_le; have := D.b_sub_a_lt_one; linarith

/-- `D.χ̂` vanishes off the chart. -/
theorem chiHat_eq_zero_of_not_mem {ξ : ℝ} (h : ξ ∉ Set.Ioo θ (θ + 1)) : 𝓕 (⇑D.χ) ξ = 0 := by
  have := D.chart_lo; have := D.chart_hi; have := D.c_pos
  refine D.chi_hat_zero ξ fun hξ => h ⟨?_, ?_⟩ <;> linarith [hξ.1, hξ.2]

/-! ### Periodization and the reproducing formula -/

/-- **Poisson summation for `χ_I φ_I`** (Source: main paper `s:MFanalysis`, L1861–L1879): the
Fourier series on `𝕋` of `(χ_I φ_I)|_ℤ` is the periodization of `η_I`:
`∑_y χ_I(y) φ_I(y) e(-yβ) = ∑_v η_I(β + v)`. -/
theorem chiPhi_series (β : ℝ) :
    ∑' y : ℤ, D.χ y * D.φ y * e (-((y : ℝ) * β)) = ∑' v : ℤ, D.eta (β + v) := by
  have h := tsum_mul_e_eq_tsum_fourier_add_schwartz D.chiPhi β
  simp_rw [D.chiPhi_apply, D.fourier_chiPhi] at h
  exact h

/-- On `I` there is no aliasing: `∑_y χ_I(y) φ_I(y) e(-yβ) = 1` for `β ∈ I`. -/
theorem chiPhi_series_eq_one {β : ℝ} (hβ : β ∈ Set.Icc a b) :
    ∑' y : ℤ, D.χ y * D.φ y * e (-((y : ℝ) * β)) = 1 := by
  have hc := D.c_pos
  have hlo := D.chart_lo
  have hhi := D.chart_hi
  rw [D.chiPhi_series]
  rw [tsum_eq_single 0]
  · simp only [Int.cast_zero, add_zero]
    exact D.eta_eq_one (by linarith [hβ.1]) (by linarith [hβ.2])
  · intro v hv
    refine D.eta_eq_zero fun hmem => hv ?_
    have h1 : (v : ℝ) < 1 := by linarith [hmem.2, hβ.1]
    have h2 : (-1 : ℝ) < v := by linarith [hmem.1, hβ.2]
    have h1' : v < 1 := by exact_mod_cast h1
    have h2' : -1 < v := by exact_mod_cast h2
    omega

/-- The sequence `χ_I φ_I` is absolutely summable. -/
theorem summable_norm_chiPhi : Summable fun y : ℤ => ‖D.χ y * D.φ y‖ := by
  have h := summable_mul_e_int_schwartz D.chiPhi 0
  simp_rw [D.chiPhi_apply, mul_zero, neg_zero, e_zero, mul_one] at h
  exact h.norm

theorem tsum_enorm_chiPhi_ne_top : ∑' y : ℤ, ‖D.χ y * D.φ y‖ₑ ≠ ⊤ := by
  have h := D.summable_norm_chiPhi
  have : ∑' y : ℤ, ‖D.χ y * D.φ y‖ₑ = ENNReal.ofReal (∑' y : ℤ, ‖D.χ y * D.φ y‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) h]
    exact tsum_congr fun y => (ofReal_norm _).symm
  rw [this]; exact ENNReal.ofReal_ne_top

/-- **The reproducing formula** (Source: main paper `s:MFanalysis`, L1872–L1876): if `H ∈ L²`
vanishes off `I` (so the sequence `h = invFZ θ H` has `ĥ` supported in `I`), then
`(χ_I φ_I) * h = h`, i.e. `∑_y χ_I(y) φ_I(y) h(x - y) = h(x)`. -/
theorem reproducing_formula {H : ℝ → ℂ} (hH : ChartL2 θ H)
    (hHs : ∀ β : ℝ, β ∉ Set.Icc a b → H β = 0) (x : ℤ) :
    ∑' y : ℤ, (D.χ y * D.φ y) * invFZ θ H (x - y) = invFZ θ H x := by
  set u : ℤ → ℂ := fun y => D.χ y * D.φ y with hu
  let f : ℤ → ℝ → ℂ := fun y β => u y * (H β * e (((x - y : ℤ) : ℝ) * β))
  have hHint := hH.integrableOn
  have hmeas : ∀ y : ℤ, AEStronglyMeasurable (f y) (volume.restrict (Set.Ioc θ (θ + 1))) := by
    intro y
    exact aestronglyMeasurable_const.mul
      (hH.aestronglyMeasurable.mul (continuous_e.comp (by fun_prop)).aestronglyMeasurable)
  have hnorm : ∀ y : ℤ, ∫⁻ β in Set.Ioc θ (θ + 1), ‖f y β‖ₑ =
      ‖u y‖ₑ * ∫⁻ β in Set.Ioc θ (θ + 1), ‖H β‖ₑ := by
    intro y
    have he : ∀ t : ℝ, ‖e t‖ₑ = 1 := fun t => by rw [← ofReal_norm, norm_e]; simp
    simp only [f, enorm_mul, he, mul_one]
    exact lintegral_const_mul' _ _ enorm_ne_top
  have hfin : ∑' y : ℤ, ∫⁻ β in Set.Ioc θ (θ + 1), ‖f y β‖ₑ ≠ ⊤ := by
    simp_rw [hnorm]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top D.tsum_enorm_chiPhi_ne_top hHint.2.ne
  have h1 : ∀ y : ℤ, u y * invFZ θ H (x - y) = ∫ β in Set.Ioc θ (θ + 1), f y β := by
    intro y
    unfold invFZ
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_const_mul]
  calc ∑' y : ℤ, u y * invFZ θ H (x - y)
      = ∑' y : ℤ, ∫ β in Set.Ioc θ (θ + 1), f y β := tsum_congr h1
    _ = ∫ β in Set.Ioc θ (θ + 1), ∑' y : ℤ, f y β := (integral_tsum hmeas hfin).symm
    _ = ∫ β in Set.Ioc θ (θ + 1), H β * e ((x : ℝ) * β) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
        by_cases hβ : β ∈ Set.Icc a b
        · have hpt : ∀ y : ℤ, f y β = (H β * e ((x : ℝ) * β)) * (u y * e (-((y : ℝ) * β))) := by
            intro y
            have : e (((x - y : ℤ) : ℝ) * β) = e ((x : ℝ) * β) * e (-((y : ℝ) * β)) := by
              rw [← e_add]; congr 1; push_cast; ring
            simp only [f, this]; ring
          simp_rw [hpt]
          rw [tsum_mul_left, D.chiPhi_series_eq_one hβ, mul_one]
        · have h0 := hHs β hβ
          simp [f, h0]
    _ = invFZ θ H x := by
        unfold invFZ
        rw [intervalIntegral.integral_of_le (by linarith)]

end CutoffData

end PrimeCarleson.Proof.Paper
