module

public import PrimeCarleson.Proof.Paper.P6a.KQH
public import PrimeCarleson.Proof.Paper.P6a.KQFourier

/-!
# `K_Q` as the convolution of `φ_{N(Q)}` with the tail kernel `H`

The `K_Q`-replacement (Source: main paper `p:red-var`, L1504): the paper's
`K_Q = φ_{N(Q)} * ∑_{k ≥ k₀} ψ_k` is the Fourier-multiplier definition `K_Q(x) = ∫ K̂_Q(ξ) e(xξ) dξ`
of `P5/Kernel.lean`: for every `n`, `K_Q(n) = ∫ φ_N(y) H(n - y) dy`, `φ_N(y) = N⁻¹ φ(y/N)`,
`H = ∑_{k ≥ k₀} ψ_k`. Proof: Fubini and Fourier inversion for each `ψ_k`, then summation over `k`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Paper.P5

variable (S : KQSetup)

/-- The `L¹`-normalized dilate `φ_N(y) = N⁻¹ φ(y / N)` of the cutoff, `N = N(Q)`. -/
def phiN (Q : ℕ) (y : ℝ) : ℂ :=
  (((S.P.NQ Q)⁻¹ : ℝ) : ℂ) * (S.φ.toSchwartz : ℝ → ℂ) (y / S.P.NQ Q)

theorem continuous_phiN (Q : ℕ) : Continuous (phiN S Q) := by
  unfold phiN
  exact continuous_const.mul (S.φ.toSchwartz.continuous.comp (continuous_id.div_const _))

theorem integrable_phiN (Q : ℕ) : Integrable (phiN S Q) := by
  unfold phiN
  exact (S.φ.toSchwartz.integrable.comp_div (S.P.NQ_pos Q).ne').const_mul _

/-- `∫ φ_N = 1`. -/
theorem integral_phiN (Q : ℕ) : ∫ y, phiN S Q y = 1 := by
  have hN := S.P.NQ_pos Q
  unfold phiN
  rw [integral_const_mul, Measure.integral_comp_div (S.φ.toSchwartz : ℝ → ℂ) (S.P.NQ Q),
    abs_of_pos hN, S.φ.integral_eq_one S.δ_pos]
  simp [hN.ne']

/-- `φ̂_N(ξ) = φ̂(N ξ)`. -/
theorem fourier_phiN (Q : ℕ) (ξ : ℝ) : 𝓕 (phiN S Q) ξ = S.φ.hat (S.P.NQ Q * ξ) := by
  have hN := S.P.NQ_pos Q
  unfold phiN
  rw [fourier_const_mul', fourier_comp_div _ hN]
  simp only [PhiData.hat, SchwartzMap.fourier_coe]
  push_cast
  exact inv_mul_cancel_left₀ (by exact_mod_cast hN.ne') _

theorem continuous_psiHat (ψ : PsiData) : Continuous (psiHat ψ) := by
  have hint : Integrable (psic ψ) :=
    (contDiff_psic ψ).continuous.integrable_of_hasCompactSupport (hasCompactSupport_psic ψ)
  simpa [psiHat_eq] using continuous_fourier_of_integrable hint

/-- **Per-scale convolution identity**: for every `k` and `x ∈ ℝ`,
`∫ φ̂(Nξ) ψ̂(2^k ξ) e(ξ x) dξ = ∫ φ_N(y) ψ_k(x - y) dy` (Fubini and Fourier inversion). -/
theorem conv_k (Q k : ℕ) (x : ℝ) :
    ∫ ξ : ℝ, S.φ.hat (S.P.NQ Q * ξ) * (psiHat S.ψ (2 ^ k * ξ) * e (ξ * x)) =
      ∫ y : ℝ, phiN S Q y * psiKc S.ψ k (x - y) := by
  set F : ℝ → ℝ → ℂ := fun ξ y =>
    e (-(y * ξ)) * phiN S Q y * (psiHat S.ψ (2 ^ k * ξ) * e (ξ * x)) with hF
  have hcF : Continuous (Function.uncurry F) := by
    have he1 : Continuous fun z : ℝ × ℝ => e (-(z.2 * z.1)) :=
      Common.continuous_e.comp (by fun_prop)
    have he2 : Continuous fun z : ℝ × ℝ => e (z.1 * x) :=
      Common.continuous_e.comp (by fun_prop)
    have h3 : Continuous fun z : ℝ × ℝ => phiN S Q z.2 :=
      (continuous_phiN S Q).comp continuous_snd
    have h4 : Continuous fun z : ℝ × ℝ => psiHat S.ψ (2 ^ k * z.1) :=
      (continuous_psiHat S.ψ).comp (continuous_const.mul continuous_fst)
    exact (he1.mul h3).mul (h4.mul he2)
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine Integrable.mono' (((integrable_psiHat_dilate S.ψ k).norm).mul_prod
      (integrable_phiN S Q).norm) hcF.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    refine le_of_eq ?_
    simp only [Function.uncurry, hF, norm_mul, Goal0.norm_e]
    ring
  have h1 : ∀ ξ : ℝ, S.φ.hat (S.P.NQ Q * ξ) * (psiHat S.ψ (2 ^ k * ξ) * e (ξ * x)) =
      ∫ y : ℝ, F ξ y := by
    intro ξ
    rw [← fourier_phiN S Q ξ, fourier_eq_integral_e, ← integral_mul_const]
  simp_rw [h1]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ∫ ξ : ℝ, F ξ y = phiN S Q y * psiKc S.ψ k (x - y)
  rw [psiK_inv S.ψ k (x - y), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [hF]
  have : e (-(y * ξ)) * e (ξ * x) = e (ξ * (x - y)) := by
    rw [← Goal0.e_add]; congr 1; ring
  calc e (-(y * ξ)) * phiN S Q y * (psiHat S.ψ (2 ^ k * ξ) * e (ξ * x))
      = phiN S Q y * psiHat S.ψ (2 ^ k * ξ) * (e (-(y * ξ)) * e (ξ * x)) := by ring
    _ = phiN S Q y * (psiHat S.ψ (2 ^ k * ξ) * e (ξ * (x - y))) := by rw [this]; ring

/-- **`K_Q = φ_N * H` on `ℤ`**: `K_Q(n) = ∫ φ_N(y) H(n - y) dy`, `H = ∑_{k ≥ ⌈Q^{1/D₀}⌉} ψ_k`. -/
theorem KQz_eq_conv (Q : ℕ) (n : ℤ) :
    S.KQz Q n = ∫ y : ℝ, phiN S Q y * ((Hfn S.ψ (S.P.kmin Q) ((n : ℝ) - y) : ℝ) : ℂ) := by
  obtain ⟨M, hM0, hM⟩ := P5.exists_norm_le_schwartz (𝓕 S.φ.toSchwartz)
  obtain ⟨B, hB0, hB⟩ := exists_bound_psi S.ψ
  set k₀ := S.P.kmin Q with hk₀
  set F : ℕ → ℝ → ℂ := fun i ξ =>
    S.φ.hat (S.P.NQ Q * ξ) * (psiHat S.ψ (2 ^ (k₀ + i) * ξ) * e (ξ * n)) with hF
  have hφc : Continuous fun ξ : ℝ => S.φ.hat (S.P.NQ Q * ξ) :=
    (𝓕 S.φ.toSchwartz).continuous.comp (continuous_const.mul continuous_id)
  have hFint : ∀ i, Integrable (F i) := fun i =>
    (integrable_mul_e (integrable_psiHat_dilate S.ψ (k₀ + i)) _).bdd_mul (c := M)
      hφc.aestronglyMeasurable (ae_of_all _ fun ξ => hM _)
  have hFsum : Summable fun i => ∫ ξ, ‖F i ξ‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) ((summable_integral_norm_psiHat S.ψ k₀).mul_left M)
    rw [← integral_const_mul]
    refine integral_mono (hFint i).norm ((integrable_psiHat_dilate S.ψ (k₀ + i)).norm.const_mul M)
      fun ξ => ?_
    simp only [hF, norm_mul, Goal0.norm_e, mul_one]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have h1 : S.KQz Q n = ∑' i, ∫ ξ, F i ξ := by
    rw [integral_tsum_of_summable_integral_norm hFint hFsum]
    unfold KQSetup.KQz KQSetup.KQ KQSetup.KQhat
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hF]
    rw [tsum_mul_left, tsum_mul_right]
    unfold psiTail
    rw [mul_comm (n : ℝ) ξ]
    ring
  set G : ℕ → ℝ → ℂ := fun i y => phiN S Q y * psiKc S.ψ (k₀ + i) ((n : ℝ) - y) with hG
  have hgc : ∀ i : ℕ, Continuous fun y : ℝ => psiKc S.ψ (k₀ + i) ((n : ℝ) - y) := fun i =>
    (contDiff_psiKc S.ψ (k₀ + i)).continuous.comp (continuous_const.sub continuous_id)
  have hgb : ∀ (i : ℕ) (y : ℝ), ‖psiKc S.ψ (k₀ + i) ((n : ℝ) - y)‖ ≤
      B * ((2 : ℝ) ^ (k₀ + i))⁻¹ := by
    intro i y
    simp only [psiKc, Complex.norm_real, Real.norm_eq_abs]
    exact abs_psiK_le hB _ _
  have hGint : ∀ i, Integrable (G i) := fun i =>
    (integrable_phiN S Q).mul_bdd (c := B * ((2 : ℝ) ^ (k₀ + i))⁻¹) (hgc i).aestronglyMeasurable
      (ae_of_all _ fun y => hgb i y)
  set m₀ : ℝ := ∫ y, ‖phiN S Q y‖ with hm₀
  have hGsum : Summable fun i => ∫ y, ‖G i y‖ := by
    have hgeo : Summable fun i : ℕ => m₀ * (B * ((2 : ℝ) ^ k₀)⁻¹) * ((1 / 2 : ℝ) ^ i) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) hgeo
    calc ∫ y, ‖G i y‖ ≤ ∫ y, ‖phiN S Q y‖ * (B * ((2 : ℝ) ^ (k₀ + i))⁻¹) :=
          integral_mono (hGint i).norm ((integrable_phiN S Q).norm.mul_const _) fun y => by
            simp only [hG, norm_mul]
            exact mul_le_mul_of_nonneg_left (hgb i y) (norm_nonneg _)
      _ = m₀ * (B * ((2 : ℝ) ^ (k₀ + i))⁻¹) := by rw [integral_mul_const]
      _ = m₀ * (B * ((2 : ℝ) ^ k₀)⁻¹) * ((1 / 2 : ℝ) ^ i) := by
          rw [pow_add, mul_inv, one_div, inv_pow]; ring
  have h2 : ∀ i, ∫ ξ, F i ξ = ∫ y, G i y := fun i => conv_k S Q (k₀ + i) (n : ℝ)
  rw [h1, tsum_congr h2, integral_tsum_of_summable_integral_norm hGint hGsum]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hG]
  rw [tsum_mul_left]
  congr 1
  unfold Hfn psiKc
  rw [Complex.ofReal_tsum]

end PrimeCarleson.Proof.Paper
