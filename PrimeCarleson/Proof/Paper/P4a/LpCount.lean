module

public import PrimeCarleson.Proof.Common.HausdorffYoung
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# `ℓ^p(ℤ)` norms of `ℝ≥0∞`-valued sequences as tsums

Auxiliary API for `Paper/P4a/` (`sources/Variational_Carleson.tex` L907-L1183): the paper's `ℓ^p`
norm of a function on `ℤ` is `eLpNorm F (ENNReal.ofReal p) Measure.count`, and the variations
`V^r(…)(x)` are `ℝ≥0∞`-valued. This file
records `eLpNorm F (ofReal p) count = (∑' x, ‖F x‖ₑ ^ p)^{1/p}` and the elementary manipulations of
such norms (the `p = 2` case, translation invariance, Minkowski's inequality for finite sums).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- `ℓ^p(ℤ)` norms as tsums: `‖F‖_{ℓ^p} = (∑' x, ‖F x‖ₑ^p)^{1/p}` for `0 < p`. -/
theorem eLpNorm_count_eq_tsum {E : Type*} [NormedAddCommGroup E] (g : ℤ → E) {p : ℝ}
    (hp : 0 < p) :
    eLpNorm g (ENNReal.ofReal p) Measure.count = (∑' x, ‖g x‖ₑ ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top
    StronglyMeasurable.of_discrete.aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal hp.le]

/-- The same for `ℝ≥0∞`-valued sequences. -/
theorem eLpNorm_count_eq_tsum_enn (F : ℤ → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    eLpNorm F (ENNReal.ofReal p) Measure.count = (∑' x, F x ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top
    StronglyMeasurable.of_discrete.aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal hp.le]
  simp

/-- For a sequence carried by a finite set `S`, `∑' x, ‖g x‖ₑ^p = ofReal (∑_{x ∈ S} ‖g x‖^p)`. -/
theorem tsum_enorm_rpow_eq_ofReal_sum {E : Type*} [NormedAddCommGroup E] {g : ℤ → E}
    {S : Finset ℤ} (hS : ∀ x ∉ S, g x = 0) {p : ℝ} (hp : 0 < p) :
    ∑' x, ‖g x‖ₑ ^ p = ENNReal.ofReal (∑ x ∈ S, ‖g x‖ ^ p) := by
  rw [tsum_eq_sum (s := S) (fun n hn => by simp [hS n hn, ENNReal.zero_rpow_of_pos hp]),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

/-- The case `p = 2`: `∑' x, ‖g x‖ₑ^2 = ofReal (∑_{x ∈ S} ‖g x‖²)`. -/
theorem tsum_enorm_sq_eq_ofReal_sum {E : Type*} [NormedAddCommGroup E] {g : ℤ → E}
    {S : Finset ℤ} (hS : ∀ x ∉ S, g x = 0) :
    ∑' x, ‖g x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∑ x ∈ S, ‖g x‖ ^ 2) := by
  rw [tsum_enorm_rpow_eq_ofReal_sum hS two_pos]
  simp only [Real.rpow_two]

/-- The `ℓ²` norm of a sequence carried by a finite set `S`. -/
theorem eLpNorm_two_count_eq {E : Type*} [NormedAddCommGroup E] {g : ℤ → E} {S : Finset ℤ}
    (hS : ∀ x ∉ S, g x = 0) :
    eLpNorm g 2 Measure.count = ENNReal.ofReal (∑ x ∈ S, ‖g x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, eLpNorm_count_eq_tsum g two_pos, tsum_enorm_sq_eq_ofReal_sum hS]

/-- The `ℓ²` norm of an `ℝ≥0∞`-valued sequence. -/
theorem eLpNorm_two_count_enn (F : ℤ → ℝ≥0∞) :
    eLpNorm F 2 Measure.count = (∑' x, F x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, eLpNorm_count_eq_tsum_enn F two_pos]

/-- Pointwise domination gives domination of `ℓ^p` norms. -/
theorem eLpNorm_count_mono_enn {F G : ℤ → ℝ≥0∞} (h : ∀ x, F x ≤ G x) (p : ℝ≥0∞) :
    eLpNorm F p Measure.count ≤ eLpNorm G p Measure.count :=
  eLpNorm_mono_enorm StronglyMeasurable.of_discrete.aestronglyMeasurable h

/-- Homogeneity of the `ℓ^p` norm for a constant in `ℝ≥0∞`. -/
theorem eLpNorm_count_const_mul (c : ℝ≥0∞) (F : ℤ → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => c * F x) (ENNReal.ofReal p) Measure.count =
      c * eLpNorm F (ENNReal.ofReal p) Measure.count := by
  rw [eLpNorm_count_eq_tsum_enn _ hp, eLpNorm_count_eq_tsum_enn _ hp]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- Minkowski's inequality in `ℓ^p(ℤ)`, `1 ≤ p`, for finite sums of `ℝ≥0∞`-valued sequences. -/
theorem eLpNorm_count_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℤ → ℝ≥0∞) {p : ℝ}
    (hp : 1 ≤ p) :
    eLpNorm (fun x => ∑ i ∈ s, F i x) (ENNReal.ofReal p) Measure.count ≤
      ∑ i ∈ s, eLpNorm (F i) (ENNReal.ofReal p) Measure.count := by
  have := eLpNorm_sum_le (μ := Measure.count) (s := s) (f := F) (ENNReal.one_le_ofReal.2 hp)
  simpa [Finset.sum_fn] using this

end PrimeCarleson.Proof.Paper
