module

public import PrimeCarleson.Proof.Paper.P5.PsiHatDeriv
public import PrimeCarleson.Proof.Paper.P5.Variation

/-!
# Uniform bounded variation of the multiplier `K̂_Q`

Source: main paper `p:global-shell-var`, L2028–L2029; main paper `s:red`, L1694–L1695 (the paper
does not prove the uniform bound; it is proved here; the bound is also used at L2247).

Proof. By `PsiHatDeriv.lean` the partial sums `S_{a,b} = ∑_{k ∈ [a, b)} ψ̂(2^k β)` have derivative
`-2πi (G_b - G_a)`, `G_j = 2^j λ̂(2^j ·)`, with `‖G_j‖_{L¹} = ‖λ̂‖_{L¹} =: Λ₁` for every `j`
(`λ(t) = 1 - t ∑_{k ≥ 0} ψ_k(t)` is compactly supported because `∑_{k ≥ 0} ψ_k(t) = 1/t` for
`|t| ≥ 1`). Hence `V(S_{a,b}) ≤ 4π Λ₁` and `|S_{a,b}| ≤ 2π Λ₁`, uniformly in `a ≤ b`, and by lower
semicontinuity of the variation the tail `psiTail ψ k₀ = ∑_{k ≥ k₀} ψ̂(2^k ·)` has `V ≤ 4π Λ₁`,
`|·| ≤ 2π Λ₁`, uniformly in `k₀`. The product with `φ̂(N ·)` (`V(φ̂(N ·)) = V(φ̂) ≤ ‖φ̂'‖_{L¹}`
for every `N > 0`) is bounded by `eVariationOn_smul_le`. The constant
`4πΛ₁‖φ̂‖_∞ + 2πΛ₁‖φ̂'‖_{L¹}` depends on `ψ` and `φ` only, not on `Q`, `D₀`, `ε`, `δ`.
The rescaled kernels `K_{Q,d}(m) = d K_Q(d m)`, `d ≤ Q`, have multiplier `K̂_Q(ξ/d)`, with the same
variation (`KQdhat`, a monotone reparametrization).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ContDiff Real

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper.P5

open PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

variable (ψ : PsiData)

/-! ### The partial sums -/

theorem tendsto_psiHat_dilate_atTop (k : ℕ) :
    Tendsto (fun β : ℝ => psiHat ψ (2 ^ k * β)) atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := norm_psiHat_le ψ
  refine squeeze_zero_norm (fun β => hB _) ?_
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : Tendsto (fun β : ℝ => 2 ^ k * β) atTop atTop := tendsto_id.const_mul_atTop hp
  have h2 : Tendsto (fun β : ℝ => 1 + (2 ^ k * β) ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ ((tendsto_pow_atTop two_ne_zero).comp h1)
  exact tendsto_const_nhds.div_atTop h2

theorem tendsto_psiHat_dilate_atBot (k : ℕ) :
    Tendsto (fun β : ℝ => psiHat ψ (2 ^ k * β)) atBot (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := norm_psiHat_le ψ
  refine squeeze_zero_norm (fun β => hB _) ?_
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : Tendsto (fun β : ℝ => -(2 ^ k * β)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp (tendsto_id.const_mul_atBot hp)
  have h2 : Tendsto (fun β : ℝ => 1 + (2 ^ k * β) ^ 2) atBot atTop := by
    have := tendsto_atTop_add_const_left _ (1 : ℝ) ((tendsto_pow_atTop two_ne_zero).comp h1)
    simpa only [Function.comp_def, neg_sq] using this
  exact tendsto_const_nhds.div_atTop h2

theorem tendsto_Spart_atTop (a b : ℕ) : Tendsto (Spart ψ a b) atTop (𝓝 0) := by
  have := tendsto_finsetSum (Finset.Ico a b) fun k _ => tendsto_psiHat_dilate_atTop ψ k
  have e : Spart ψ a b = fun β => ∑ k ∈ Finset.Ico a b, psiHat ψ (2 ^ k * β) := rfl
  rw [e]
  simpa using this

theorem tendsto_Spart_atBot (a b : ℕ) : Tendsto (Spart ψ a b) atBot (𝓝 0) := by
  have := tendsto_finsetSum (Finset.Ico a b) fun k _ => tendsto_psiHat_dilate_atBot ψ k
  have e : Spart ψ a b = fun β => ∑ k ∈ Finset.Ico a b, psiHat ψ (2 ^ k * β) := rfl
  rw [e]
  simpa using this

theorem continuous_deriv_Spart (a b : ℕ) :
    Continuous fun β => -2 * (π : ℂ) * Complex.I * (Gfun ψ b β - Gfun ψ a β) :=
  continuous_const.mul ((continuous_Gfun ψ b).sub (continuous_Gfun ψ a))

theorem integrable_deriv_Spart (a b : ℕ) :
    Integrable fun β => -2 * (π : ℂ) * Complex.I * (Gfun ψ b β - Gfun ψ a β) :=
  ((integrable_Gfun ψ b).sub (integrable_Gfun ψ a)).const_mul _

/-- `‖(S_{a,b})'‖_{L¹} ≤ 4π Λ₁` for every `a ≤ b`. -/
theorem integral_norm_deriv_Spart_le (a b : ℕ) :
    ∫ β, ‖-2 * (π : ℂ) * Complex.I * (Gfun ψ b β - Gfun ψ a β)‖ ≤ 4 * π * Lam1 ψ := by
  have h : ∀ β, ‖-2 * (π : ℂ) * Complex.I * (Gfun ψ b β - Gfun ψ a β)‖ ≤
      2 * π * (‖Gfun ψ b β‖ + ‖Gfun ψ a β‖) := by
    intro β
    rw [norm_mul]
    have : ‖-2 * (π : ℂ) * Complex.I‖ = 2 * π := by
      simp [abs_of_pos Real.pi_pos]
    rw [this]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
  calc ∫ β, ‖-2 * (π : ℂ) * Complex.I * (Gfun ψ b β - Gfun ψ a β)‖
      ≤ ∫ β, 2 * π * (‖Gfun ψ b β‖ + ‖Gfun ψ a β‖) :=
        integral_mono ((integrable_deriv_Spart ψ a b).norm)
          (((integrable_Gfun ψ b).norm.add (integrable_Gfun ψ a).norm).const_mul _) h
    _ = 4 * π * Lam1 ψ := by
        rw [integral_const_mul, integral_add (integrable_Gfun ψ b).norm (integrable_Gfun ψ a).norm,
          integral_norm_Gfun, integral_norm_Gfun]
        ring

/-- `V(S_{a,b}) ≤ 4π Λ₁`. -/
theorem eVariationOn_Spart_le {a b : ℕ} (hab : a ≤ b) :
    eVariationOn (Spart ψ a b) Set.univ ≤ ENNReal.ofReal (4 * π * Lam1 ψ) :=
  (eVariationOn_le_integral (hasDerivAt_Spart ψ hab) (continuous_deriv_Spart ψ a b)
    (integrable_deriv_Spart ψ a b)).trans
    (ENNReal.ofReal_le_ofReal (integral_norm_deriv_Spart_le ψ a b))

/-- `|S_{a,b}(β)| ≤ 2π Λ₁`. -/
theorem norm_Spart_le {a b : ℕ} (hab : a ≤ b) (β : ℝ) : ‖Spart ψ a b β‖ ≤ 2 * π * Lam1 ψ := by
  have h := norm_le_half_integral (hasDerivAt_Spart ψ hab) (continuous_deriv_Spart ψ a b)
    (integrable_deriv_Spart ψ a b) (tendsto_Spart_atTop ψ a b) (tendsto_Spart_atBot ψ a b) β
  have := integral_norm_deriv_Spart_le ψ a b
  linarith

/-! ### The tail `∑_{k ≥ k₀} ψ̂(2^k β)` -/

theorem hasSum_psiTail (k₀ : ℕ) (β : ℝ) :
    HasSum (fun i : ℕ => psiHat ψ (2 ^ (k₀ + i) * β)) (psiTail ψ k₀ β) :=
  (Summable.of_norm (summable_psiTail ψ k₀ β)).hasSum

theorem tendsto_Spart_psiTail (k₀ : ℕ) (β : ℝ) :
    Tendsto (fun n : ℕ => Spart ψ k₀ (k₀ + n) β) atTop (𝓝 (psiTail ψ k₀ β)) := by
  have h := (hasSum_psiTail ψ k₀ β).tendsto_sum_nat
  refine h.congr fun n => ?_
  simp only [Spart]
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- `|∑_{k ≥ k₀} ψ̂(2^k β)| ≤ 2π Λ₁`, uniformly in `k₀` and `β`. -/
theorem norm_psiTail_le (k₀ : ℕ) (β : ℝ) : ‖psiTail ψ k₀ β‖ ≤ 2 * π * Lam1 ψ :=
  le_of_tendsto' (tendsto_Spart_psiTail ψ k₀ β).norm fun _ =>
    norm_Spart_le ψ (Nat.le_add_right _ _) β

/-- `V(∑_{k ≥ k₀} ψ̂(2^k ·)) ≤ 4π Λ₁`, uniformly in `k₀`. -/
theorem eVariationOn_psiTail_le (k₀ : ℕ) :
    eVariationOn (psiTail ψ k₀) Set.univ ≤ ENNReal.ofReal (4 * π * Lam1 ψ) :=
  eVariationOn_le_of_forall (F := fun n => Spart ψ k₀ (k₀ + n)) (tendsto_Spart_psiTail ψ k₀)
    fun _ => eVariationOn_Spart_le ψ (Nat.le_add_right _ _)

/-! ### The product with `φ̂(N ·)` -/

/-- The total variation of a Schwartz function is at most `‖f'‖_{L¹}`. -/
theorem eVariationOn_schwartz_le (f : 𝓢(ℝ, ℂ)) :
    eVariationOn (f : ℝ → ℂ) Set.univ ≤ ENNReal.ofReal (∫ x, ‖deriv (f : ℝ → ℂ) x‖) := by
  refine eVariationOn_le_integral (fun x => (f.differentiableAt (x := x)).hasDerivAt) ?_ ?_
  · exact (SchwartzMap.derivCLM ℝ ℂ f).continuous
  · exact (SchwartzMap.derivCLM ℝ ℂ f).integrable

theorem exists_norm_le_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M :=
  ⟨‖f.toBoundedContinuousFunction‖, norm_nonneg _,
    fun x => f.toBoundedContinuousFunction.norm_coe_le_norm x⟩

/-- **Uniform bounded variation of `φ̂(N β) ∑_{k ≥ k₀} ψ̂(2^k β)`**: for `ψ` and `φ` there is `C`
such that for all `N > 0` and `k₀`, the function is bounded by `C` and has total variation at
most `C`. -/
theorem exists_bv_bound (φ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ), 0 < N → ∀ k₀ : ℕ,
      (∀ β, ‖𝓕 φ (N * β) * psiTail ψ k₀ β‖ ≤ C) ∧
      eVariationOn (fun β => 𝓕 φ (N * β) * psiTail ψ k₀ β) Set.univ ≤ ENNReal.ofReal C := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_le_schwartz (𝓕 φ)
  set T : ℝ := ∫ x, ‖deriv ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ with hT
  have hT0 : 0 ≤ T := integral_nonneg fun _ => norm_nonneg _
  have hΛ := Lam1_nonneg ψ
  refine ⟨4 * π * Lam1 ψ * A + 2 * π * Lam1 ψ * T, by positivity, fun N hN k₀ => ⟨fun β => ?_, ?_⟩⟩
  · rw [norm_mul]
    calc ‖𝓕 φ (N * β)‖ * ‖psiTail ψ k₀ β‖ ≤ A * (2 * π * Lam1 ψ) :=
          mul_le_mul (hA _) (norm_psiTail_le ψ k₀ β) (norm_nonneg _) hA0
      _ ≤ _ := by nlinarith [Real.pi_pos, mul_nonneg hΛ hA0, mul_nonneg hΛ hT0, Real.pi_pos.le]
  · -- the variation of `φ̂(N ·)`
    have hu : eVariationOn (fun β => 𝓕 φ (N * β)) Set.univ ≤ ENNReal.ofReal T := by
      have h1 := eVariationOn.comp_eq_of_monotoneOn (fun x => 𝓕 φ x) (fun β : ℝ => N * β)
        (t := Set.univ) (fun a _ b _ hab => mul_le_mul_of_nonneg_left hab hN.le)
      have h2 : (fun β : ℝ => N * β) '' Set.univ = Set.univ := by
        ext y
        simp only [Set.image_univ, Set.mem_range, Set.mem_univ, iff_true]
        exact ⟨y / N, by field_simp⟩
      rw [h2] at h1
      have h3 : (fun β => 𝓕 φ (N * β)) = (fun x => 𝓕 φ x) ∘ (fun β : ℝ => N * β) := rfl
      rw [h3, h1]
      exact eVariationOn_schwartz_le (𝓕 φ)
    have hsm := eVariationOn_smul_le (f := fun β => 𝓕 φ (N * β)) (g := psiTail ψ k₀)
      (s := Set.univ) (C := ENNReal.ofReal A) (D := ENNReal.ofReal (2 * π * Lam1 ψ))
      (fun x _ => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hA _))
      (fun x _ => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_psiTail_le ψ k₀ x))
    have e1 : ((fun β => 𝓕 φ (N * β)) • psiTail ψ k₀) =
        fun β => 𝓕 φ (N * β) * psiTail ψ k₀ β := rfl
    rw [e1] at hsm
    refine hsm.trans ?_
    calc ENNReal.ofReal A * eVariationOn (psiTail ψ k₀) Set.univ +
          ENNReal.ofReal (2 * π * Lam1 ψ) * eVariationOn (fun β => 𝓕 φ (N * β)) Set.univ
        ≤ ENNReal.ofReal A * ENNReal.ofReal (4 * π * Lam1 ψ) +
          ENNReal.ofReal (2 * π * Lam1 ψ) * ENNReal.ofReal T := by
          gcongr
          · exact eVariationOn_psiTail_le ψ k₀
      _ = ENNReal.ofReal (4 * π * Lam1 ψ * A + 2 * π * Lam1 ψ * T) := by
          rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

end PrimeCarleson.Proof.Paper.P5
