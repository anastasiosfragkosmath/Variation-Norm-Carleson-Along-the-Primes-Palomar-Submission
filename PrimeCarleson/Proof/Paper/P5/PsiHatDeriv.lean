module

public import PrimeCarleson.Proof.Paper.P5.PsiHat

/-!
# Derivatives of the partial sums `∑_{k ∈ [a, b)} ψ̂(2^k β)`

`sources/Variational_Carleson.tex` L1480-L1483, L2028-L2029 (Source: main paper `p:red-var`,
L1476–L1483; main paper `p:global-shell-var`, L2028–L2029; main paper `s:red`, L1694–L1695). With
`λ = 1 - t H(t)` of `Telescope.lean` (compactly supported, smooth),
`λ̂` is integrable, `G_j(β) := 2^j λ̂(2^j β)` has `‖G_j‖_{L¹} = ‖λ̂‖_{L¹}` for every `j`, and

`d/dβ ∑_{k ∈ [a, b)} ψ̂(2^k β) = -2πi (G_b(β) - G_a(β))`

(`hasDerivAt_Spart`), by `t ψ_k(t) = λ(t/2^{k+1}) - λ(t/2^k)`. Hence `‖(S_{a,b})'‖_{L¹} ≤
4π ‖λ̂‖_{L¹}` uniformly in `a ≤ b` (`integral_norm_deriv_Spart_le`), and, since `S_{a,b} → 0` at
`±∞`, `|S_{a,b}(β)| ≤ 4π ‖λ̂‖_{L¹}` (`norm_Spart_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped FourierTransform SchwartzMap ContDiff Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper.P5

open PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

variable (ψ : PsiData)

/-- `λ` as a complex-valued function. -/
def lamC (t : ℝ) : ℂ := ((lamFun ψ t : ℝ) : ℂ)

/-- `λ̂`. -/
def lamHat (u : ℝ) : ℂ := 𝓕 (lamC ψ) u

/-- `G_k(β) = 2^k λ̂(2^k β)`, the Fourier transform of `λ(·/2^k)`. -/
def Gfun (k : ℕ) (β : ℝ) : ℂ := (2 : ℂ) ^ k * lamHat ψ (2 ^ k * β)

/-- The partial sum `∑_{k ∈ [a, b)} ψ̂(2^k β)`. -/
def Spart (a b : ℕ) (β : ℝ) : ℂ := ∑ k ∈ Finset.Ico a b, psiHat ψ (2 ^ k * β)

theorem contDiff_lamC : ContDiff ℝ ∞ (lamC ψ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_lamFun ψ)

theorem hasCompactSupport_lamC : HasCompactSupport (lamC ψ) :=
  (hasCompactSupport_lamFun ψ).comp_left Complex.ofReal_zero

theorem integrable_lamC : Integrable (lamC ψ) :=
  (contDiff_lamC ψ).continuous.integrable_of_hasCompactSupport (hasCompactSupport_lamC ψ)

/-- `λ̂` is integrable (`λ ∈ C_c^∞`). -/
theorem integrable_lamHat : Integrable (lamHat ψ) :=
  integrable_fourier_of_contDiff_two ((contDiff_lamC ψ).of_le (by norm_num))
    (hasCompactSupport_lamC ψ)

theorem continuous_lamHat : Continuous (lamHat ψ) :=
  continuous_fourier_of_integrable (integrable_lamC ψ)

/-- `Λ₁ := ‖λ̂‖_{L¹}`. -/
def Lam1 : ℝ := ∫ u, ‖lamHat ψ u‖

theorem Lam1_nonneg : 0 ≤ Lam1 ψ := integral_nonneg fun _ => norm_nonneg _

theorem continuous_Gfun (k : ℕ) : Continuous (Gfun ψ k) := by
  unfold Gfun
  exact continuous_const.mul ((continuous_lamHat ψ).comp (continuous_const.mul continuous_id))

theorem integrable_Gfun (k : ℕ) : Integrable (Gfun ψ k) := by
  have h := (integrable_lamHat ψ).comp_mul_left' (R := (2 : ℝ) ^ k) (by positivity)
  exact (h.const_mul ((2 : ℂ) ^ k))

/-- `‖G_k‖_{L¹} = ‖λ̂‖_{L¹}`. -/
theorem integral_norm_Gfun (k : ℕ) : ∫ β, ‖Gfun ψ k β‖ = Lam1 ψ := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h : ∀ β, ‖Gfun ψ k β‖ = (2 : ℝ) ^ k * ‖lamHat ψ (2 ^ k * β)‖ := by
    intro β
    simp [Gfun]
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun u => ‖lamHat ψ u‖), smul_eq_mul,
    abs_inv, abs_of_pos hp, Lam1]
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

/-! ### Linearity of `𝓕` for integrable functions -/

theorem integrable_e_mul {f : ℝ → ℂ} (hf : Integrable f) (β : ℝ) :
    Integrable fun x : ℝ => e (-(x * β)) * f x := by
  refine Integrable.bdd_mul hf ?_ (c := 1) (Filter.Eventually.of_forall fun x => ?_)
  · exact (continuous_e.comp (continuous_id.mul continuous_const).neg).aestronglyMeasurable
  · simp [norm_e]

theorem fourier_sub' {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (β : ℝ) :
    𝓕 (fun t : ℝ => f t - g t) β = 𝓕 f β - 𝓕 g β := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e, fourier_eq_integral_e,
    ← integral_sub (integrable_e_mul hf β) (integrable_e_mul hg β)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- `t ψ_k(t) = λ(t / 2^{k+1}) - λ(t / 2^k)` in `ℂ`. -/
theorem ofReal_mul_psiKc (k : ℕ) (t : ℝ) :
    (t : ℂ) * psiKc ψ k t = lamC ψ (t / 2 ^ (k + 1)) - lamC ψ (t / 2 ^ k) := by
  have h := mul_psiK_eq_sub_lamFun ψ k t
  simp only [psiKc, lamC]
  exact_mod_cast h

/-- `d/dβ ψ̂(2^k β) = -2πi (G_{k+1}(β) - G_k(β))`. -/
theorem hasDerivAt_psiHat_dilate (k : ℕ) (β : ℝ) :
    HasDerivAt (fun b : ℝ => psiHat ψ (2 ^ k * b))
      (-2 * π * Complex.I * (Gfun ψ (k + 1) β - Gfun ψ k β)) β := by
  have hfun : (fun b : ℝ => psiHat ψ (2 ^ k * b)) = 𝓕 (psiKc ψ k) := by
    funext b
    rw [psiK_hat]
  rw [hfun]
  have hf : Integrable (psiKc ψ k) :=
    (contDiff_psiKc ψ k).continuous.integrable_of_hasCompactSupport (hasCompactSupport_psiKc ψ k)
  have hf' : Integrable (fun x : ℝ => x • psiKc ψ k x) := by
    have hcs : HasCompactSupport (fun x : ℝ => (x : ℂ) * psiKc ψ k x) := by
      refine HasCompactSupport.intro (K := Set.Icc (-(2 : ℝ) ^ k) (2 ^ k)) isCompact_Icc
        fun t ht => ?_
      have : (2 : ℝ) ^ k ≤ |t| := by
        by_contra h
        exact ht (Set.mem_Icc.2 (abs_le.1 (not_le.1 h).le))
      simp [psiKc, ψ.psiK_eq_zero_of_ge this]
    have hct : Continuous fun x : ℝ => (x : ℂ) * psiKc ψ k x :=
      Complex.continuous_ofReal.mul (contDiff_psiKc ψ k).continuous
    have : Integrable (fun x : ℝ => (x : ℂ) * psiKc ψ k x) volume :=
      hct.integrable_of_hasCompactSupport hcs
    simpa only [Complex.real_smul] using this
  have h := Real.hasDerivAt_fourier hf hf' β
  convert h using 1
  have hpf : ∀ x : ℝ, (-2 * (π : ℂ) * Complex.I * (x : ℂ)) • psiKc ψ k x =
      (-2 * π * Complex.I : ℂ) * (lamC ψ (x / 2 ^ (k + 1)) - lamC ψ (x / 2 ^ k)) := by
    intro x
    rw [← ofReal_mul_psiKc, smul_eq_mul]
    ring
  simp_rw [hpf]
  rw [fourier_const_mul', fourier_sub']
  · rw [fourier_comp_div _ (by positivity), fourier_comp_div _ (by positivity)]
    simp only [Gfun, lamHat]
    push_cast
    rfl
  · exact (integrable_lamC ψ).comp_div (by positivity)
  · exact (integrable_lamC ψ).comp_div (by positivity)

/-- The derivative of the partial sum: `-2πi (G_b - G_a)`. -/
theorem hasDerivAt_Spart {a b : ℕ} (hab : a ≤ b) (β : ℝ) :
    HasDerivAt (Spart ψ a b) (-2 * π * Complex.I * (Gfun ψ b β - Gfun ψ a β)) β := by
  induction b, hab using Nat.le_induction with
  | base =>
    have h0 : Spart ψ a a = fun _ => 0 := by
      funext x
      simp [Spart]
    rw [h0, sub_self, mul_zero]
    exact hasDerivAt_const β (0 : ℂ)
  | succ b hab ih =>
    have h := ih.add (hasDerivAt_psiHat_dilate ψ b β)
    have e1 : Spart ψ a (b + 1) = fun x => Spart ψ a b x + psiHat ψ (2 ^ b * x) := by
      funext x
      simp only [Spart]
      rw [Finset.sum_Ico_succ_top hab]
    rw [e1]
    convert h using 1
    ring

end PrimeCarleson.Proof.Paper.P5
