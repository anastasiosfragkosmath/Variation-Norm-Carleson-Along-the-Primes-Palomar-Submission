module

public import PrimeCarleson.Proof.Paper.P4a.Multiplier
public import PrimeCarleson.Proof.Paper.P4a.LpCount

/-!
# The square function of the dyadic modulation increments

Source: main paper `e:Dsfbound`, L952–L961 (proof L963–L1022); consumer: the sum over scales of
`l:crudeV2lambda`, L1043–L1052.

For `K ≥ 1`, `α ∈ 𝕋` and `0 ≤ s < K` the increments are
`D_{K,α,s} f := A_{α+(s+1)/K} f - A_{α+s/K} f` (`modIncrement`) and the claim is
`‖(∑_{s<K} |D_{K,α,s} f|²)^{1/2}‖_{ℓ²} ≲ min{1, (N/K)^{1/2}} ‖w‖_{L²([N])} ‖f‖_{ℓ²}`
(`eLpNorm_modIncrementSq_le`, the absolute constant is `2π`). The proof is Plancherel
(`Common.sum_norm_sq_eq_integral`) together with the pointwise multiplier bound
`Paper.multiplierIncrement_le` (`e:multsf`): the multiplier of `D_{K,α,s}` is
`multiplierIncrement N w K α s` (`fourierZ_incrementFinsupp`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The increment `D_{K,α,s} f(x) := A_{α+(s+1)/K} f(x) - A_{α+s/K} f(x)` (L952-L956). -/
def modIncrement (N : ℕ+) (w f : ℤ → ℂ) (K : ℕ) (α : ℝ) (s : ℕ) (x : ℤ) : ℂ :=
  modAverage N w f (α + ((s : ℝ) + 1) / K) x - modAverage N w f (α + (s : ℝ) / K) x

/-- The square function `(∑_{s<K} |D_{K,α,s} f(x)|²)^{1/2}` of the dyadic increments
(L957-L959), `ℝ≥0∞`-valued. -/
def modIncrementSq (N : ℕ+) (w f : ℤ → ℂ) (K : ℕ) (α : ℝ) (x : ℤ) : ℝ≥0∞ :=
  (∑ s ∈ Finset.range K, ‖modIncrement N w f K α s x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- The Fourier series is additive. -/
theorem fourierZ_sub (u v : ℤ →₀ ℂ) (ξ : ℝ) :
    fourierZ (u - v) ξ = fourierZ u ξ - fourierZ v ξ := by
  have hS : (u - v).support ⊆ u.support ∪ v.support := Finsupp.support_sub
  rw [fourierZ_eq_sum_of_support_subset _ hS,
    fourierZ_eq_sum_of_support_subset u Finset.subset_union_left,
    fourierZ_eq_sum_of_support_subset v Finset.subset_union_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [sub_mul]

/-- `D_{K,α,s} F` as a finitely supported sequence. -/
def incrementFinsupp (N : ℕ+) (w : ℤ → ℂ) (K : ℕ) (α : ℝ) (s : ℕ) (F : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  convZ F (avgKernel N w (α + ((s : ℝ) + 1) / K)) - convZ F (avgKernel N w (α + (s : ℝ) / K))

/-- The values of `incrementFinsupp` are those of `modIncrement`. -/
theorem incrementFinsupp_apply (N : ℕ+) (w : ℤ → ℂ) (K : ℕ) (α : ℝ) (s : ℕ) (F : ℤ →₀ ℂ)
    (x : ℤ) : incrementFinsupp N w K α s F x = modIncrement N w (⇑F) K α s x := by
  simp only [incrementFinsupp, Finsupp.coe_sub, Pi.sub_apply, modIncrement,
    modAverage_eq_convZ]

/-- The multiplier of `D_{K,α,s}` is `m(ξ-α-(s+1)/K) - m(ξ-α-s/K)`. -/
theorem fourierZ_incrementFinsupp (N : ℕ+) (w : ℤ → ℂ) (K : ℕ) (α : ℝ) (s : ℕ) (F : ℤ →₀ ℂ)
    (ξ : ℝ) :
    fourierZ (incrementFinsupp N w K α s F) ξ =
      multiplierIncrement N w K α s ξ * fourierZ F ξ := by
  unfold incrementFinsupp multiplierIncrement
  rw [fourierZ_sub, fourierZ_modAverage, fourierZ_modAverage, ← sub_mul, sub_sub, sub_sub]

/-- Plancherel for the square function: for every finitely supported `F`,
`∑_{s<K} ∑_x |D_{K,α,s} F(x)|² ≤ M² ∑_x |F(x)|²` with `M = 2π min{1,(N/K)^{1/2}} ‖w‖_{L²([N])}`. -/
theorem sum_sum_norm_sq_increment_le (N : ℕ+) (w : ℤ → ℂ) {K : ℕ} (hK : 0 < K) (α : ℝ)
    (F : ℤ →₀ ℂ) :
    ∑ s ∈ Finset.range K, ∑ x ∈ (incrementFinsupp N w K α s F).support,
        ‖incrementFinsupp N w K α s F x‖ ^ 2 ≤
      (2 * Real.pi * min 1 (Real.sqrt ((N : ℝ) / K)) * lpNormOn 2 (bracket N) w) ^ 2 *
        ∑ x ∈ F.support, ‖F x‖ ^ 2 := by
  set M : ℝ := 2 * Real.pi * min 1 (Real.sqrt ((N : ℝ) / K)) * lpNormOn 2 (bracket N) w with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ min 1 (Real.sqrt ((N : ℝ) / K)) := le_min zero_le_one (Real.sqrt_nonneg _)
    rw [hM]
    have := lpNormOn_nonneg 2 (bracket N) w
    positivity
  have hMsq : ∀ ξ, ∑ s ∈ Finset.range K, ‖multiplierIncrement N w K α s ξ‖ ^ 2 ≤ M ^ 2 := by
    intro ξ
    exact (Real.sqrt_le_iff.1 (multiplierIncrement_le N w hK α ξ)).2
  have hP : ∀ s : ℕ, ∑ x ∈ (incrementFinsupp N w K α s F).support,
      ‖incrementFinsupp N w K α s F x‖ ^ 2 =
        ∫ ξ in (0 : ℝ)..1, ‖fourierZ (incrementFinsupp N w K α s F) ξ‖ ^ 2 :=
    fun s => sum_norm_sq_eq_integral _
  simp_rw [hP]
  have hint : ∀ s ∈ Finset.range K, IntervalIntegrable
      (fun ξ : ℝ => ‖fourierZ (incrementFinsupp N w K α s F) ξ‖ ^ 2) MeasureTheory.volume 0 1 :=
    fun s _ => ((continuous_fourierZ _).norm.pow 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finsetSum hint, sum_norm_sq_eq_integral F,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_finsetSum _ fun s _ =>
      ((continuous_fourierZ (incrementFinsupp N w K α s F)).norm.pow 2)).intervalIntegrable _ _)
    ?_ fun ξ _ => ?_
  · exact (continuous_const.mul ((continuous_fourierZ F).norm.pow 2)).intervalIntegrable _ _
  · simp_rw [fourierZ_incrementFinsupp, norm_mul, mul_pow]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hMsq ξ) (sq_nonneg _)

/-- **`e:Dsfbound`** (L952-L961, proof L963-L1022): for `N ≥ 1`, `w : [N] → ℂ`, a finitely
supported `f : ℤ → ℂ`, an integer `K ≥ 1` and `α ∈ 𝕋` (here any real `α`),
`‖(∑_{s<K} |D_{K,α,s} f|²)^{1/2}‖_{ℓ²} ≤ 2π min{1,(N/K)^{1/2}} ‖w‖_{L²([N])} ‖f‖_{ℓ²}`,
uniformly in `K` and `α` (absolute constant `2π`). Source: main paper `e:Dsfbound`, L952–L961. -/
theorem eLpNorm_modIncrementSq_le (N : ℕ+) (w : ℤ → ℂ) {K : ℕ} (hK : 0 < K) (α : ℝ)
    (f : ℤ → ℂ) (hf : (Function.support f).Finite) :
    eLpNorm (modIncrementSq N w f K α) 2 Measure.count ≤
      ENNReal.ofReal
          (2 * Real.pi * min 1 (Real.sqrt ((N : ℝ) / K)) * lpNormOn 2 (bracket N) w) *
        eLpNorm f 2 Measure.count := by
  classical
  set F : ℤ →₀ ℂ := Finsupp.ofSupportFinite f hf with hF
  have hFf : ⇑F = f := rfl
  set M : ℝ := 2 * Real.pi * min 1 (Real.sqrt ((N : ℝ) / K)) * lpNormOn 2 (bracket N) w with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ min 1 (Real.sqrt ((N : ℝ) / K)) := le_min zero_le_one (Real.sqrt_nonneg _)
    rw [hM]
    have := lpNormOn_nonneg 2 (bracket N) w
    positivity
  have hD : ∀ s x, modIncrement N w f K α s x = incrementFinsupp N w K α s F x := by
    intro s x
    rw [incrementFinsupp_apply, hFf]
  have hsum : ∀ s, ∑' x, ‖modIncrement N w f K α s x‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (∑ x ∈ (incrementFinsupp N w K α s F).support,
        ‖incrementFinsupp N w K α s F x‖ ^ 2) := by
    intro s
    have := tsum_enorm_sq_eq_ofReal_sum (g := fun x => incrementFinsupp N w K α s F x)
      (S := (incrementFinsupp N w K α s F).support)
      (fun x hx => Finsupp.notMem_support_iff.1 hx)
    simpa only [hD] using this
  have hmain : ∑' x, modIncrementSq N w f K α x ^ (2 : ℝ) ≤
      ENNReal.ofReal (M ^ 2 * ∑ x ∈ F.support, ‖F x‖ ^ 2) := by
    have h1 : ∀ x, modIncrementSq N w f K α x ^ (2 : ℝ) =
        ∑ s ∈ Finset.range K, ‖modIncrement N w f K α s x‖ₑ ^ (2 : ℝ) := by
      intro x
      unfold modIncrementSq
      rw [← ENNReal.rpow_mul]
      norm_num
    simp_rw [h1]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [hsum]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
    exact ENNReal.ofReal_le_ofReal (sum_sum_norm_sq_increment_le N w hK α F)
  rw [eLpNorm_two_count_enn, eLpNorm_two_count_eq (g := f) (S := F.support)
    (fun x hx => Finsupp.notMem_support_iff.1 hx)]
  calc (∑' x, modIncrementSq N w f K α x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (M ^ 2 * ∑ x ∈ F.support, ‖F x‖ ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hmain (by norm_num)
    _ = ENNReal.ofReal M * ENNReal.ofReal (∑ x ∈ F.support, ‖f x‖ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_pow hM0, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
        rfl

end PrimeCarleson.Proof.Paper
