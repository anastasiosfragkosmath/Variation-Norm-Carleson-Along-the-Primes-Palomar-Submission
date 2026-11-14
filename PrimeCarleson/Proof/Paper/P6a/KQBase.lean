module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.Paper.P5.ErrorKQ
public import PrimeCarleson.Proof.Paper.P5.PsiHat

/-!
# Fourier-analytic facts on `ψ̂` and on the tail `∑_{k ≥ k₀} ψ̂(2^k ·)`

Inputs of the error estimates for the `K_Q`-replacement (Source: main paper `p:red-var`,
L1476–L1507): `ψ̂` is integrable, `ψ_k(t) = ∫ ψ̂(2^k ξ) e(ξ t) dξ` (Fourier inversion for the smooth
compactly supported `ψ_k`), the tail `∑_{k ≥ k₀} ψ̂(2^k ·)` is integrable with
`‖·‖_{L¹} ≤ 2^{1-k₀} ‖ψ̂‖_{L¹}`, and `2^{-⌈Q^{1/D₀}⌉} ≤ C_A Q^{-A}`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Paper.P5

variable (ψ : PsiData)

/-- `‖ψ̂‖_{L¹}`. -/
def psiHatL1 : ℝ := ∫ u, ‖psiHat ψ u‖

/-- `ψ̂` is integrable. -/
theorem integrable_psiHat : Integrable (psiHat ψ) := by
  have := integrable_fourier_of_contDiff_two ((contDiff_psic ψ).of_le (by norm_num))
    (hasCompactSupport_psic ψ)
  simpa [psiHat_eq] using this

/-- `ψ̂(2^k ·)` is integrable. -/
theorem integrable_psiHat_dilate (k : ℕ) : Integrable (fun ξ : ℝ => psiHat ψ (2 ^ k * ξ)) :=
  (integrable_psiHat ψ).comp_mul_left' (by positivity)

/-- `∫ |ψ̂(2^k ξ)| dξ = 2^{-k} ‖ψ̂‖_{L¹}`. -/
theorem integral_norm_psiHat_dilate (k : ℕ) :
    ∫ ξ : ℝ, ‖psiHat ψ (2 ^ k * ξ)‖ = ((2 : ℝ) ^ k)⁻¹ * psiHatL1 ψ := by
  rw [Measure.integral_comp_mul_left (fun u => ‖psiHat ψ u‖) ((2 : ℝ) ^ k)]
  simp [psiHatL1, abs_of_pos (show (0 : ℝ) < 2 ^ k by positivity)]

/-- `‖ψ̂‖_{L¹} ≥ 0`. -/
theorem psiHatL1_nonneg : 0 ≤ psiHatL1 ψ := integral_nonneg fun _ => norm_nonneg _

/-- **Fourier inversion for `ψ_k`**: `ψ_k(t) = ∫ ψ̂(2^k ξ) e(ξ t) dξ`. -/
theorem psiK_inv (k : ℕ) (t : ℝ) :
    psiKc ψ k t = ∫ ξ : ℝ, psiHat ψ (2 ^ k * ξ) * e (ξ * t) := by
  have h := fourier_inversion_of_contDiff_two ((contDiff_psiKc ψ k).of_le (by norm_num))
    (hasCompactSupport_psiKc ψ k) t
  simp_rw [psiK_hat] at h
  exact h

/-- The tail multiplier is measurable. -/
theorem measurable_psiTail (k₀ : ℕ) : Measurable (psiTail ψ k₀) := by
  refine measurable_of_tendsto_metrizable (f := fun n => Spart ψ k₀ (k₀ + n)) (fun n => ?_)
    (tendsto_pi_nhds.2 (tendsto_Spart_psiTail ψ k₀))
  exact Continuous.measurable (continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_Spart ψ (Nat.le_add_right k₀ n) x).continuousAt)

/-- The series of the `L¹` norms `∫ |ψ̂(2^{k₀+i} ξ)| dξ` is summable. -/
theorem summable_integral_norm_psiHat (k₀ : ℕ) :
    Summable fun i : ℕ => ∫ ξ : ℝ, ‖psiHat ψ (2 ^ (k₀ + i) * ξ)‖ := by
  simp_rw [integral_norm_psiHat_dilate, pow_add, mul_inv, mul_assoc]
  refine Summable.mul_left _ ?_
  have : Summable fun i : ℕ => ((1 : ℝ) / 2) ^ i :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa [one_div, inv_pow, mul_comm] using this.mul_right (psiHatL1 ψ)

/-- `∑_i ∫ |ψ̂(2^{k₀+i} ξ)| dξ = 2 · 2^{-k₀} ‖ψ̂‖_{L¹}`. -/
theorem tsum_integral_norm_psiHat (k₀ : ℕ) :
    ∑' i : ℕ, ∫ ξ : ℝ, ‖psiHat ψ (2 ^ (k₀ + i) * ξ)‖ = 2 * ((2 : ℝ) ^ k₀)⁻¹ * psiHatL1 ψ := by
  simp_rw [integral_norm_psiHat_dilate, pow_add, mul_inv]
  have h : ∑' i : ℕ, ((2 : ℝ) ^ i)⁻¹ = 2 := by
    simpa [one_div, inv_pow] using tsum_geometric_two
  rw [show (fun i : ℕ => ((2 : ℝ) ^ k₀)⁻¹ * ((2 : ℝ) ^ i)⁻¹ * psiHatL1 ψ) =
      fun i : ℕ => (((2 : ℝ) ^ k₀)⁻¹ * psiHatL1 ψ) * ((2 : ℝ) ^ i)⁻¹ by funext i; ring,
    tsum_mul_left, h]
  ring

/-- The tail multiplier is integrable, with
`∫ |∑_{k ≥ k₀} ψ̂(2^k ξ)| dξ ≤ 2 · 2^{-k₀} ‖ψ̂‖_{L¹}`. -/
theorem integrable_psiTail_and_bound (k₀ : ℕ) :
    Integrable (psiTail ψ k₀) ∧
      ∫ ξ, ‖psiTail ψ k₀ ξ‖ ≤ 2 * ((2 : ℝ) ^ k₀)⁻¹ * psiHatL1 ψ := by
  have hF : ∀ i : ℕ, Integrable (fun ξ : ℝ => psiHat ψ (2 ^ (k₀ + i) * ξ)) :=
    fun i => integrable_psiHat_dilate ψ (k₀ + i)
  have hs := summable_integral_norm_psiHat ψ k₀
  have hlint : ∫⁻ ξ, ‖psiTail ψ k₀ ξ‖ₑ ≤
      ENNReal.ofReal (2 * ((2 : ℝ) ^ k₀)⁻¹ * psiHatL1 ψ) := by
    calc ∫⁻ ξ, ‖psiTail ψ k₀ ξ‖ₑ ≤ ∫⁻ ξ, ∑' i : ℕ, ‖psiHat ψ (2 ^ (k₀ + i) * ξ)‖ₑ :=
          lintegral_mono fun ξ => by
            unfold psiTail
            exact enorm_tsum_le_tsum_enorm
      _ = ∑' i : ℕ, ∫⁻ ξ, ‖psiHat ψ (2 ^ (k₀ + i) * ξ)‖ₑ :=
          lintegral_tsum fun i => (hF i).1.enorm
      _ = ∑' i : ℕ, ENNReal.ofReal (∫ ξ, ‖psiHat ψ (2 ^ (k₀ + i) * ξ)‖) := by
          refine tsum_congr fun i => ?_
          rw [ofReal_integral_norm_eq_lintegral_enorm (hF i)]
      _ = ENNReal.ofReal (∑' i : ℕ, ∫ ξ, ‖psiHat ψ (2 ^ (k₀ + i) * ξ)‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _) hs).symm
      _ = _ := by rw [tsum_integral_norm_psiHat]
  have hint : Integrable (psiTail ψ k₀) :=
    ⟨(measurable_psiTail ψ k₀).aestronglyMeasurable,
      lt_of_le_of_lt hlint ENNReal.ofReal_lt_top⟩
  refine ⟨hint, ?_⟩
  have h2 := ofReal_integral_norm_eq_lintegral_enorm hint
  rw [← h2] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff (by have := psiHatL1_nonneg ψ; positivity)).1 hlint

/-- **`2^{-⌈Q^{1/D₀}⌉}` decays faster than every power of `Q`**: for `D₀ > 0` and `A` there is
`C` with `(2^{k₀})⁻¹ ≤ C Q^{-A}` whenever `k₀ ≥ Q^{1/D₀}`, `Q ≥ 1`. -/
theorem inv_two_pow_le_rpow_neg {D₀ : ℝ} (hD : 0 < D₀) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q k₀ : ℕ), 1 ≤ Q → (Q : ℝ) ^ (1 / D₀) ≤ k₀ →
      ((2 : ℝ) ^ k₀)⁻¹ ≤ C * (Q : ℝ) ^ (-A) := by
  set m : ℕ := ⌈max A 0 * D₀⌉₊ with hm
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨(m.factorial : ℝ) * (Real.log 2) ^ (-(m : ℝ)), by positivity, fun Q k₀ hQ hk => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  set y : ℝ := (Q : ℝ) ^ (1 / D₀) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hQ0 _
  have hz : 0 < Real.log 2 * y := by positivity
  have h1 := Real.pow_div_factorial_le_exp (Real.log 2 * y) hz.le m
  have h2 : ((2 : ℝ) ^ k₀)⁻¹ ≤ Real.exp (-(Real.log 2 * y)) := by
    rw [Real.exp_neg, ← Real.rpow_natCast, Real.rpow_def_of_pos two_pos]
    refine inv_anti₀ (Real.exp_pos _) (Real.exp_le_exp.2 ?_)
    have : (y : ℝ) ≤ k₀ := hk
    nlinarith
  have h3 : Real.exp (-(Real.log 2 * y)) ≤ (m.factorial : ℝ) * ((Real.log 2 * y) ^ m)⁻¹ := by
    rw [Real.exp_neg]
    have hpos : 0 < (Real.log 2 * y) ^ m / m.factorial := by positivity
    calc (Real.exp (Real.log 2 * y))⁻¹ ≤ ((Real.log 2 * y) ^ m / m.factorial)⁻¹ :=
          inv_anti₀ hpos h1
      _ = _ := by rw [inv_div, div_eq_mul_inv]
  have h4 : ((Real.log 2 * y) ^ m)⁻¹ = (Real.log 2) ^ (-(m : ℝ)) * (Q : ℝ) ^ (-(m : ℝ) / D₀) := by
    rw [mul_pow, mul_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hl2.le,
      hy, ← Real.rpow_mul hQ0.le, ← Real.rpow_neg hQ0.le]
    congr 2
    field_simp
  have h5 : (Q : ℝ) ^ (-(m : ℝ) / D₀) ≤ (Q : ℝ) ^ (-A) := by
    refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
    have : max A 0 * D₀ ≤ m := Nat.le_ceil _
    have h6 : A ≤ max A 0 := le_max_left _ _
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ hD]
    nlinarith
  calc ((2 : ℝ) ^ k₀)⁻¹ ≤ (m.factorial : ℝ) * ((Real.log 2 * y) ^ m)⁻¹ := h2.trans h3
    _ = (m.factorial : ℝ) * ((Real.log 2) ^ (-(m : ℝ)) * (Q : ℝ) ^ (-(m : ℝ) / D₀)) := by rw [h4]
    _ ≤ (m.factorial : ℝ) * ((Real.log 2) ^ (-(m : ℝ)) * (Q : ℝ) ^ (-A)) := by
        gcongr
    _ = _ := by ring

end PrimeCarleson.Proof.Paper
