module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.Paper.P5.ErrorKQ
public import PrimeCarleson.Proof.Paper.P5.PsiHat
public import PrimeCarleson.Proof.Paper.P6a.KQBase
public import PrimeCarleson.Proof.Common.FourierZ

/-!
# The `K_Q`-replacement error weight and its Fourier representation

Source: main paper `p:red-var`, L1476–L1507. The error weight is
`E_Q(n) = ∑_{k ≥ ⌈Q^{1/D₀}⌉} ψ_k(n) - K_Q(n)` (`errW`); its multiplier on `ℝ` is `KQerr`
(`P5/ErrorKQ.lean`), `E_Q(x) = ∫ KQerr_Q(ξ) e(xξ) dξ`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The error weight `E_Q(n) = ∑_{k ≥ k₀} ψ_k(n) - K_Q(n)`, `k₀ = ⌈Q^{1/D₀}⌉` (L1483-L1493). -/
def errW (S : KQSetup) (Q : ℕ) (n : ℤ) : ℂ := psiTailZ S.ψ (S.P.kmin Q) n - S.KQz Q n

/-- `psiTail` is integrable. -/
theorem integrable_psiTail (ψ : PsiData) (k₀ : ℕ) : Integrable (psiTail ψ k₀) :=
  (integrable_psiTail_and_bound ψ k₀).1

/-- An integrable function times a character is integrable. -/
theorem integrable_mul_e {g : ℝ → ℂ} (hg : Integrable g) (a : ℝ) :
    Integrable (fun ξ : ℝ => g ξ * e (ξ * a)) := by
  refine Integrable.mono' hg.norm (hg.1.mul
    (Common.continuous_e.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun ξ => ?_)
  simp [Goal0.norm_e]

/-- **Fourier representation of the error weight**: `E_Q(n) = ∫ KQerr_Q(ξ) e(nξ) dξ` for
`n ∈ ℤ` (Fourier inversion for the `ψ_k`, summed over `k`, minus the definition of `K_Q`). -/
theorem errW_eq_integral (S : KQSetup) (Q : ℕ) (n : ℤ) :
    errW S Q n = ∫ ξ : ℝ, S.KQerr Q ξ * e ((n : ℝ) * ξ) := by
  set k₀ := S.P.kmin Q with hk₀
  have h1 : psiTailZ S.ψ k₀ n = ∫ ξ : ℝ, psiTail S.ψ k₀ ξ * e (ξ * n) := by
    have hF : ∀ i : ℕ, Integrable (fun ξ : ℝ => psiHat S.ψ (2 ^ (k₀ + i) * ξ) * e (ξ * n)) :=
      fun i => integrable_mul_e (integrable_psiHat_dilate S.ψ (k₀ + i)) _
    have hs : Summable fun i : ℕ =>
        ∫ ξ : ℝ, ‖psiHat S.ψ (2 ^ (k₀ + i) * ξ) * e (ξ * n)‖ := by
      simpa [norm_mul, Goal0.norm_e] using summable_integral_norm_psiHat S.ψ k₀
    have h := integral_tsum_of_summable_integral_norm hF hs
    unfold psiTailZ
    calc ∑' i : ℕ, psiKz S.ψ (k₀ + i) n
        = ∑' i : ℕ, ∫ ξ : ℝ, psiHat S.ψ (2 ^ (k₀ + i) * ξ) * e (ξ * n) :=
          tsum_congr fun i => psiK_inv S.ψ (k₀ + i) n
      _ = ∫ ξ : ℝ, ∑' i : ℕ, psiHat S.ψ (2 ^ (k₀ + i) * ξ) * e (ξ * n) := h
      _ = ∫ ξ : ℝ, psiTail S.ψ k₀ ξ * e (ξ * n) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
          simp only [psiTail]
          rw [tsum_mul_right]
  have h2 : S.KQz Q n = ∫ ξ : ℝ, S.KQhat Q ξ * e (ξ * n) := by
    unfold KQSetup.KQz KQSetup.KQ
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [mul_comm ξ]
  unfold errW
  rw [h1, h2, ← integral_sub (integrable_mul_e (integrable_psiTail S.ψ k₀) _)
    (integrable_mul_e (S.integrable_KQhat Q) _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [KQSetup.KQerr, ← sub_mul, hk₀, mul_comm ξ]

/-- The multiplier `KQerr_Q` is integrable, with `‖KQerr_Q‖_{L¹}` at most `C_A Q^{-A}` for every
`A` (`‖(1 - φ̂(N ·)) ∑_{k ≥ k₀} ψ̂(2^k ·)‖_{L¹} ≤ (1 + ‖φ̂‖_∞) 2^{1-k₀} ‖ψ̂‖_{L¹}`,
`2^{-k₀} ≤ 2^{-Q^{1/D₀}}`). -/
theorem integral_norm_KQerr_le (S : KQSetup) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q → Integrable (S.KQerr Q) ∧
      ∫ ξ, ‖S.KQerr Q ξ‖ ≤ C * (Q : ℝ) ^ (-A) := by
  obtain ⟨M, hM0, hM⟩ := P5.exists_norm_le_schwartz (𝓕 S.φ.toSchwartz)
  obtain ⟨C₁, hC₁0, hC₁⟩ := inv_two_pow_le_rpow_neg S.P.D₀_pos A
  have hL := psiHatL1_nonneg S.ψ
  refine ⟨(1 + M) * (2 * C₁ * psiHatL1 S.ψ), by positivity, fun Q hQ => ?_⟩
  set k₀ := S.P.kmin Q with hk₀
  obtain ⟨hint, hbound⟩ := integrable_psiTail_and_bound S.ψ k₀
  have hint' : Integrable (S.KQerr Q) := by
    have : S.KQerr Q = fun ξ => psiTail S.ψ k₀ ξ - S.KQhat Q ξ := rfl
    rw [this]
    exact hint.sub (S.integrable_KQhat Q)
  refine ⟨hint', ?_⟩
  have hpt : ∀ ξ, ‖S.KQerr Q ξ‖ ≤ (1 + M) * ‖psiTail S.ψ k₀ ξ‖ := by
    intro ξ
    rw [S.KQerr_eq, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖1 - S.φ.hat (S.P.NQ Q * ξ)‖ ≤ ‖(1 : ℂ)‖ + ‖S.φ.hat (S.P.NQ Q * ξ)‖ := norm_sub_le _ _
      _ ≤ 1 + M := by
          simp only [norm_one]
          exact add_le_add le_rfl (hM _)
  have hk : (Q : ℝ) ^ (1 / S.P.D₀) ≤ k₀ := S.P.rpow_le_kmin Q
  calc ∫ ξ, ‖S.KQerr Q ξ‖ ≤ ∫ ξ, (1 + M) * ‖psiTail S.ψ k₀ ξ‖ :=
        integral_mono hint'.norm (hint.norm.const_mul _) hpt
    _ = (1 + M) * ∫ ξ, ‖psiTail S.ψ k₀ ξ‖ := integral_const_mul _ _
    _ ≤ (1 + M) * (2 * ((2 : ℝ) ^ k₀)⁻¹ * psiHatL1 S.ψ) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (1 + M) * (2 * (C₁ * (Q : ℝ) ^ (-A)) * psiHatL1 S.ψ) := by
        gcongr
        exact hC₁ Q k₀ hQ hk
    _ = _ := by ring

end PrimeCarleson.Proof.Paper
