module

public import PrimeCarleson.Proof.Paper.P5.ErrorDecay

/-!
# The total variation of the multiplier of the `K_Q`-replacement error

Source: main paper `p:red-var`, L1476–L1483: the multiplier of `∑_{k ≥ k₀} ψ_k - K_Q` is
`(1 - φ̂(N β)) ∑_{k ≥ k₀} ψ̂(2^k β)`. Since `φ̂ = 1` on `[-δ/2, δ/2]`, `1 - φ̂(N ·)` vanishes for
`|β| ≤ β₀ := δ/(2N)`, where only the far tail of the `ψ̂(2^k ·)`, `k ≥ k₀`, is seen.

`eVariationOn_error_le`: for every `m ≥ 1` there is `K = K(ψ, φ, m)` such that for all `N > 0`
and `k₀`, the total variation of `(1 - φ̂(N ·)) ∑_{k ≥ k₀} ψ̂(2^k ·)` is at most
`K (2^{k₀} β₀)^{-m}`. Proof: partial sums are `C¹` with derivative `-2πi (G_b - G_a)`
(`PsiHatDeriv.lean`), the pointwise decay `|S_{a,b}(β)| ≲_m (2^a|β|)^{-m}`
(`ErrorDecay.lean`), the moments of `λ̂`, the fundamental theorem of calculus and lower
semicontinuity of the variation.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ContDiff Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper.P5

open PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

variable (ψ : PsiData)

theorem norm_deriv_Spart_le (a b : ℕ) (β : ℝ) :
    ‖-2 * (π : ℂ) * Complex.I * (Gfun ψ b β - Gfun ψ a β)‖ ≤
      2 * π * (‖Gfun ψ b β‖ + ‖Gfun ψ a β‖) := by
  rw [norm_mul]
  have : ‖-2 * (π : ℂ) * Complex.I‖ = 2 * π := by
    simp [abs_of_pos Real.pi_pos]
  rw [this]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)

/-- The pointwise bound of the derivative of the partial error `E_n = (1 - φ̂(N ·)) S_n` by an
integrable function `g` (`g` is the explicit majorant used in `eVariationOn_error_le`). -/
theorem eVariationOn_error_partial_le (F : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ ξ : ℝ, |ξ| ≤ δ / 2 → F ξ = 1) {m : ℕ} (_hm : 1 ≤ m) {A : ℝ} (hA : ∀ x, ‖F x‖ ≤ A)
    {Cm : ℝ} (hCm : ∀ (a b : ℕ) (β : ℝ), β ≠ 0 →
      ‖Spart ψ a b β‖ ≤ Cm * (((2 : ℝ) ^ a * |β|)⁻¹) ^ m)
    {N : ℝ} (hN : 0 < N) (k₀ n : ℕ) :
    eVariationOn (fun β => (1 - F (N * β)) * Spart ψ k₀ (k₀ + n) β) Set.univ ≤
      ENNReal.ofReal ((Cm * (∫ x, ‖deriv (F : ℝ → ℂ) x‖) + 2 * π * (1 + A) * 2 * Mom ψ m) *
        (((2 : ℝ) ^ k₀ * (δ / (2 * N)))⁻¹) ^ m) := by
  set β₀ : ℝ := δ / (2 * N) with hβ₀
  have hβ₀0 : 0 < β₀ := by positivity
  set R : ℝ := (2 : ℝ) ^ k₀ * β₀ with hR
  have hR0 : 0 < R := by positivity
  set cS : ℝ := Cm * (R⁻¹) ^ m with hcS
  set S : ℝ → ℂ := Spart ψ k₀ (k₀ + n) with hS
  have hCm0 : 0 ≤ Cm := by
    have := hCm 0 0 1 one_ne_zero
    simp only [Spart, Finset.Ico_self, Finset.sum_empty, norm_zero] at this
    by_contra hneg
    have hneg' : Cm < 0 := not_le.1 hneg
    have h2 : 0 < (((2 : ℝ) ^ 0 * |(1 : ℝ)|)⁻¹) ^ m := by positivity
    exact absurd this (not_le.2 (mul_neg_of_neg_of_pos hneg' h2))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hFc : Continuous (deriv (F : ℝ → ℂ)) := (SchwartzMap.derivCLM ℝ ℂ F).continuous
  have hFint : Integrable (deriv (F : ℝ → ℂ)) := (SchwartzMap.derivCLM ℝ ℂ F).integrable
  -- derivative of `E_n`
  set E' : ℝ → ℂ := fun β => -(deriv (F : ℝ → ℂ) (N * β) * N) * S β +
    (1 - F (N * β)) * (-2 * (π : ℂ) * Complex.I * (Gfun ψ (k₀ + n) β - Gfun ψ k₀ β)) with hE'
  have hE : ∀ β, HasDerivAt (fun β => (1 - F (N * β)) * S β) (E' β) β := by
    intro β
    have hlin : HasDerivAt (fun β : ℝ => N * β) N β := by
      simpa using (hasDerivAt_id β).const_mul N
    have h1 : HasDerivAt (fun β : ℝ => F (N * β)) (deriv (F : ℝ → ℂ) (N * β) * N) β := by
      have := (F.differentiableAt (x := N * β)).hasDerivAt.scomp β hlin
      rw [Complex.real_smul, mul_comm] at this
      exact this
    have h2 : HasDerivAt (fun β : ℝ => 1 - F (N * β))
        (-(deriv (F : ℝ → ℂ) (N * β) * N)) β := h1.const_sub 1
    have h3 := h2.mul (hasDerivAt_Spart ψ (Nat.le_add_right k₀ n) β)
    have h4 : HasDerivAt ((fun β : ℝ => 1 - F (N * β)) * Spart ψ k₀ (k₀ + n)) (E' β) β := by
      convert h3 using 1
    exact h4
  have hcontS : Continuous S := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact (hasDerivAt_Spart ψ (Nat.le_add_right k₀ n) x).continuousAt
  have hE'c : Continuous E' := by
    have hFcont : Continuous fun β : ℝ => F (N * β) :=
      F.continuous.comp (continuous_const.mul continuous_id)
    refine Continuous.add ?_ ?_
    · exact ((hFc.comp (continuous_const.mul continuous_id)).mul continuous_const).neg.mul hcontS
    · exact (continuous_const.sub hFcont).mul (continuous_deriv_Spart ψ k₀ (k₀ + n))
  -- the majorant
  set g : ℝ → ℝ := fun β => N * cS * ‖deriv (F : ℝ → ℂ) (N * β)‖ +
    (1 + A) * (2 * π) * ((β₀⁻¹) ^ m) * (|β| ^ m * ‖Gfun ψ (k₀ + n) β‖ + |β| ^ m * ‖Gfun ψ k₀ β‖)
    with hg
  have hgint : Integrable g := by
    refine Integrable.add ?_ ?_
    · have := (hFint.norm.comp_mul_left' (R := N) hN.ne').const_mul (N * cS)
      exact this
    · exact (((integrable_mom_Gfun ψ m (k₀ + n)).add (integrable_mom_Gfun ψ m k₀)).const_mul _)
  have hpt : ∀ β, ‖E' β‖ ≤ g β := by
    intro β
    by_cases hβ : |β| < β₀
    · have hNb : |N * β| < δ / 2 := by
        rw [abs_mul, abs_of_pos hN]
        calc N * |β| < N * β₀ := mul_lt_mul_of_pos_left hβ hN
          _ = δ / 2 := by rw [hβ₀]; field_simp
      have hF1 : F (N * β) = 1 := hF _ hNb.le
      have hdF : deriv (F : ℝ → ℂ) (N * β) = 0 := by
        have hev : (F : ℝ → ℂ) =ᶠ[nhds (N * β)] fun _ => (1 : ℂ) := by
          have : {x : ℝ | |x| < δ / 2} ∈ nhds (N * β) :=
            (isOpen_lt continuous_abs continuous_const).mem_nhds hNb
          filter_upwards [this] with x hx using hF x hx.le
        rw [hev.deriv_eq]
        simp
      simp only [hE', hF1, hdF]
      simp only [zero_mul, neg_zero, sub_self, zero_add, norm_zero]
      refine add_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) ?_
      positivity
    · have hβ : β₀ ≤ |β| := not_lt.1 hβ
      have hβ0 : β ≠ 0 := by
        intro h
        rw [h, abs_zero] at hβ
        linarith
      have hSb : ‖S β‖ ≤ cS := by
        refine (hCm k₀ (k₀ + n) β hβ0).trans ?_
        rw [hcS]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ m) hCm0
        rw [hR]
        exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hβ (by positivity))
      have hu1 : ‖1 - F (N * β)‖ ≤ 1 + A := by
        refine (norm_sub_le _ _).trans ?_
        simp only [norm_one]
        linarith [hA (N * β)]
      have hw : (1 : ℝ) ≤ (β₀⁻¹) ^ m * |β| ^ m := by
        rw [← mul_pow]
        refine one_le_pow₀ ?_
        rw [← div_eq_inv_mul, le_div_iff₀ hβ₀0]
        linarith
      have hSd := norm_deriv_Spart_le ψ k₀ (k₀ + n) β
      calc ‖E' β‖ ≤ ‖-(deriv (F : ℝ → ℂ) (N * β) * N) * S β‖ +
            ‖(1 - F (N * β)) * (-2 * (π : ℂ) * Complex.I * (Gfun ψ (k₀ + n) β - Gfun ψ k₀ β))‖ :=
            norm_add_le _ _
        _ ≤ N * cS * ‖deriv (F : ℝ → ℂ) (N * β)‖ +
            (1 + A) * (2 * π * (‖Gfun ψ (k₀ + n) β‖ + ‖Gfun ψ k₀ β‖)) := by
            refine add_le_add ?_ ?_
            · rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hN.le]
              calc ‖deriv (F : ℝ → ℂ) (N * β)‖ * N * ‖S β‖ ≤
                    ‖deriv (F : ℝ → ℂ) (N * β)‖ * N * cS :=
                    mul_le_mul_of_nonneg_left hSb (by positivity)
                _ = N * cS * ‖deriv (F : ℝ → ℂ) (N * β)‖ := by ring
            · rw [norm_mul]
              exact mul_le_mul hu1 hSd (norm_nonneg _) (by linarith)
        _ ≤ g β := by
            rw [hg]
            simp only
            refine add_le_add le_rfl ?_
            have h1 : 0 ≤ ‖Gfun ψ (k₀ + n) β‖ + ‖Gfun ψ k₀ β‖ := by positivity
            calc (1 + A) * (2 * π * (‖Gfun ψ (k₀ + n) β‖ + ‖Gfun ψ k₀ β‖))
                ≤ (1 + A) * (2 * π * ((β₀⁻¹ ^ m * |β| ^ m) *
                  (‖Gfun ψ (k₀ + n) β‖ + ‖Gfun ψ k₀ β‖))) := by
                  gcongr
                  exact le_mul_of_one_le_left h1 hw
              _ = _ := by ring
  have hE'int : Integrable E' :=
    Integrable.mono' hgint hE'c.aestronglyMeasurable (Filter.Eventually.of_forall hpt)
  refine (eVariationOn_le_integral hE hE'c hE'int).trans (ENNReal.ofReal_le_ofReal ?_)
  have hT1 : (0 : ℝ) ≤ ∫ x, ‖deriv (F : ℝ → ℂ) x‖ := integral_nonneg fun _ => norm_nonneg _
  have hMom := Mom_nonneg ψ m
  have h₁ : Integrable fun x : ℝ => N * cS * ‖deriv (F : ℝ → ℂ) (N * x)‖ :=
    (hFint.norm.comp_mul_left' (R := N) hN.ne').const_mul (N * cS)
  have h₂ : Integrable fun x : ℝ => (1 + A) * (2 * π) * ((β₀⁻¹) ^ m) *
      (|x| ^ m * ‖Gfun ψ (k₀ + n) x‖ + |x| ^ m * ‖Gfun ψ k₀ x‖) :=
    ((integrable_mom_Gfun ψ m (k₀ + n)).add (integrable_mom_Gfun ψ m k₀)).const_mul _
  have hgI : ∫ x, g x = Cm * (R⁻¹) ^ m * (∫ x, ‖deriv (F : ℝ → ℂ) x‖) +
      (1 + A) * (2 * π) * ((β₀⁻¹) ^ m) *
        ((((2 : ℝ) ^ (k₀ + n))⁻¹) ^ m * Mom ψ m + (((2 : ℝ) ^ k₀)⁻¹) ^ m * Mom ψ m) := by
    have hg' : ∀ x, g x = N * cS * ‖deriv (F : ℝ → ℂ) (N * x)‖ + (1 + A) * (2 * π) * ((β₀⁻¹) ^ m) *
        (|x| ^ m * ‖Gfun ψ (k₀ + n) x‖ + |x| ^ m * ‖Gfun ψ k₀ x‖) := fun x => rfl
    simp_rw [hg']
    rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul,
      integral_add (integrable_mom_Gfun ψ m (k₀ + n)) (integrable_mom_Gfun ψ m k₀),
      integral_mom_Gfun, integral_mom_Gfun,
      Measure.integral_comp_mul_left (fun x : ℝ => ‖deriv (F : ℝ → ℂ) x‖) N, abs_inv,
      abs_of_pos hN, smul_eq_mul]
    have : N * cS * (N⁻¹ * ∫ x, ‖deriv (F : ℝ → ℂ) x‖) =
        Cm * (R⁻¹) ^ m * (∫ x, ‖deriv (F : ℝ → ℂ) x‖) := by
      rw [hcS]
      field_simp
    rw [this]
  have h2a : (((2 : ℝ) ^ (k₀ + n))⁻¹) ^ m ≤ (((2 : ℝ) ^ k₀)⁻¹) ^ m :=
    pow_le_pow_left₀ (by positivity)
      (inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (Nat.le_add_right _ _))) m
  have hRinv : (R⁻¹) ^ m = (((2 : ℝ) ^ k₀)⁻¹) ^ m * (β₀⁻¹) ^ m := by
    rw [hR, mul_inv, mul_pow]
  have h3 : (((2 : ℝ) ^ (k₀ + n))⁻¹) ^ m * Mom ψ m + (((2 : ℝ) ^ k₀)⁻¹) ^ m * Mom ψ m ≤
      2 * ((((2 : ℝ) ^ k₀)⁻¹) ^ m * Mom ψ m) := by
    linarith only [mul_le_mul_of_nonneg_right h2a hMom]
  calc ∫ x, ‖E' x‖ ≤ ∫ x, g x := integral_mono hE'int.norm hgint hpt
    _ = _ := hgI
    _ ≤ (Cm * (∫ x, ‖deriv (F : ℝ → ℂ) x‖) + 2 * π * (1 + A) * 2 * Mom ψ m) * (R⁻¹) ^ m := by
        have hb : 0 ≤ (β₀⁻¹) ^ m := by positivity
        have h4 : (1 + A) * (2 * π) * ((β₀⁻¹) ^ m) *
            ((((2 : ℝ) ^ (k₀ + n))⁻¹) ^ m * Mom ψ m + (((2 : ℝ) ^ k₀)⁻¹) ^ m * Mom ψ m) ≤
            (1 + A) * (2 * π) * ((β₀⁻¹) ^ m) * (2 * ((((2 : ℝ) ^ k₀)⁻¹) ^ m * Mom ψ m)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        rw [hRinv] at *
        linarith only [h4]

end PrimeCarleson.Proof.Paper.P5
