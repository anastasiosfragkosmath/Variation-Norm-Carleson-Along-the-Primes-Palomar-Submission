module

public import PrimeCarleson.Proof.Paper.P5.Kernel
public import PrimeCarleson.Proof.Paper.P5.Telescope
public import PrimeCarleson.Proof.Common.FourierR

/-!
# The Fourier transform `ψ̂` and the derivatives of the partial sums `∑ ψ̂(2^k β)`

Source: main paper `s:Prelim`, L609–L612; main paper `p:red-var`, L1476–L1483; main paper
`p:global-shell-var`, L2028–L2029.

* `fourier_comp_div`: `(g(·/c))^(β) = c ĝ(cβ)`; `psiK_hat`: `(ψ_k)^(β) = ψ̂(2^k β)`;
* `psiHat_zero`: `ψ̂(0) = 0` (`ψ` is odd); `norm_psiHat_le`: `|ψ̂(u)| ≤ B/(1 + u²)`;
* `summable_psiHat_dilate`: `∑_k ψ̂(2^k β)` converges absolutely;
* `hasDerivAt_psiHat_dilate`: `d/dβ ψ̂(2^k β) = -2πi (2^{k+1} λ̂(2^{k+1} β) - 2^k λ̂(2^k β))`
  (from `t ψ_k(t) = λ(t/2^{k+1}) - λ(t/2^k)`, `Telescope.lean`), so that the partial sum over
  `k ∈ [a, b)` has derivative `-2πi (G_b - G_a)` with `G_j(β) = 2^j λ̂(2^j β)`
  (`hasDerivAt_Spart`), whose `L¹` norm is at most `4π ‖λ̂‖_{L¹}` for every `a ≤ b`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper.P5

open PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Common

variable (ψ : PsiData)

/-! ### Scaling -/

/-- `𝓕 (g(·/c)) (β) = c 𝓕 g (cβ)` for `c > 0`. -/
theorem fourier_comp_div (g : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (β : ℝ) :
    𝓕 (fun t : ℝ => g (t / c)) β = c * 𝓕 g (c * β) := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e]
  have h := Measure.integral_comp_div (fun y : ℝ => e (-(y * (c * β))) * g y) c
  rw [abs_of_pos hc, Complex.real_smul] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 2
  field_simp

/-- `𝓕 (a g) = a 𝓕 g`. -/
theorem fourier_const_mul' (a : ℂ) (g : ℝ → ℂ) (β : ℝ) :
    𝓕 (fun t : ℝ => a * g t) β = a * 𝓕 g β := by
  rw [fourier_eq_integral_e, fourier_eq_integral_e, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- `ψ_k` as a complex-valued function. -/
def psiKc (k : ℕ) (t : ℝ) : ℂ := ((psiK ψ.toFun k t : ℝ) : ℂ)

/-- `ψ` as a complex-valued function. -/
def psic (t : ℝ) : ℂ := ((ψ.toFun t : ℝ) : ℂ)

theorem psiHat_eq : psiHat ψ = 𝓕 (psic ψ) := rfl

/-- `(ψ_k)^(β) = ψ̂(2^k β)`. -/
theorem psiK_hat (k : ℕ) (β : ℝ) : 𝓕 (psiKc ψ k) β = psiHat ψ (2 ^ k * β) := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : psiKc ψ k = fun t : ℝ => (((2 : ℝ) ^ k : ℝ)⁻¹ : ℂ) * psic ψ (t / 2 ^ k) := by
    funext t
    simp only [psiKc, psic, psiK]
    rw [div_eq_mul_inv]
    push_cast
    ring_nf
  rw [h1, fourier_const_mul', fourier_comp_div _ hp, psiHat_eq]
  push_cast
  field_simp

/-- `ψ_k` is smooth. -/
theorem contDiff_psiKc (k : ℕ) : ContDiff ℝ ∞ (psiKc ψ k) :=
  Complex.ofRealCLM.contDiff.comp (ψ.contDiff_psiK k)

/-- `ψ_k` has compact support. -/
theorem hasCompactSupport_psiKc (k : ℕ) : HasCompactSupport (psiKc ψ k) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(2 : ℝ) ^ k) (2 ^ k)) isCompact_Icc fun t ht => ?_
  have : (2 : ℝ) ^ k ≤ |t| := by
    by_contra h
    exact ht (Set.mem_Icc.2 (abs_le.1 (not_le.1 h).le))
  simp [psiKc, ψ.psiK_eq_zero_of_ge this]

/-- `ψ` as a function `ℝ → ℂ` is smooth with compact support. -/
theorem contDiff_psic : ContDiff ℝ ∞ (psic ψ) := Complex.ofRealCLM.contDiff.comp ψ.contDiff

theorem hasCompactSupport_psic : HasCompactSupport (psic ψ) :=
  ψ.hasCompactSupport.comp_left Complex.ofReal_zero

/-! ### `ψ̂(0) = 0` and the decay of `ψ̂` -/

/-- `ψ̂(0) = ∫ ψ = 0` since `ψ` is odd. -/
theorem psiHat_zero : psiHat ψ 0 = 0 := by
  rw [psiHat_eq, fourier_eq_integral_e]
  simp only [mul_zero, neg_zero, e, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  have h : ∫ t : ℝ, psic ψ t = ∫ t : ℝ, psic ψ (-t) := (integral_neg_eq_self (psic ψ) volume).symm
  have h2 : ∀ t, psic ψ (-t) = - psic ψ t := by
    intro t
    simp [psic, ψ.odd]
  simp only [h2, integral_neg] at h
  have : (2 : ℂ) * ∫ t : ℝ, psic ψ t = 0 := by linear_combination h
  simpa using this

/-- Quadratic decay: `|ψ̂(u)| ≤ B / (1 + u²)`. -/
theorem norm_psiHat_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, ‖psiHat ψ u‖ ≤ B / (1 + u ^ 2) := by
  refine ⟨(∫ v, ‖psic ψ v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv (psic ψ)) v‖,
    by positivity, fun u => ?_⟩
  exact norm_fourier_le_of_contDiff_two ((contDiff_psic ψ).of_le (by norm_num))
    (hasCompactSupport_psic ψ) u

/-- `∑_k ψ̂(2^k β)` converges absolutely for each `β`. -/
theorem summable_psiHat_dilate (β : ℝ) :
    Summable fun k : ℕ => ‖psiHat ψ (2 ^ k * β)‖ := by
  by_cases hβ : β = 0
  · subst hβ
    simp [psiHat_zero]
  obtain ⟨B, hB0, hB⟩ := norm_psiHat_le ψ
  have hβ2 : 0 < β ^ 2 := by positivity
  have hgeo : Summable fun k : ℕ => B / β ^ 2 * ((1 : ℝ) / 4) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hgeo
  refine (hB _).trans ?_
  have h4 : ((1 : ℝ) / 4) ^ k = 1 / (2 ^ k) ^ 2 := by
    rw [one_div_pow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4, mul_pow, div_mul_div_comm, mul_one]
  refine div_le_div_of_nonneg_left hB0 (by positivity) ?_
  nlinarith [sq_nonneg ((2 : ℝ) ^ k * β), sq_nonneg (2 : ℝ), pow_pos (by norm_num : (0 : ℝ) < 2) k]

/-- The tail `∑_{i} ψ̂(2^{k₀ + i} β)` converges absolutely. -/
theorem summable_psiTail (k₀ : ℕ) (β : ℝ) :
    Summable fun i : ℕ => ‖psiHat ψ (2 ^ (k₀ + i) * β)‖ := by
  have := (summable_nat_add_iff k₀).2 (summable_psiHat_dilate ψ β)
  refine this.congr fun i => ?_
  simp [add_comm]

end PrimeCarleson.Proof.Paper.P5
