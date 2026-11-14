module

public import Carleson.ToMathlib.WNorm

/-!
# The distribution of a finite sum, for the quasi-triangle inequality in weak `L^p`

The distribution bound for a finite sum behind the quasi-triangle inequality for weak `L^p`, a
standard result: [O+] (L1056-L1057, L1092-L1096, L1265-L1271) sums the ten operators `S^ρ` and the
bounded number of subcollections of multitiles in `L^{p,∞}` without naming the inequality.  It is
used for the linearized theorem and for the splitting into separated subfamilies (`halfgbound`).

For functions `g_1, …, g_n` (indexed by a `Finset ι`, `n = s.card`):

* `distribution_sum_le`: `|{|g_1 + ⋯ + g_n| > t}| ≤ ∑ᵢ |{|gᵢ| > t / n}|`
  (also `measure_enorm_sum_gt_le`, and `measure_norm_sum_gt_le` for a seminormed group and a real
  level `l ≥ 0`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

section Distribution

variable {α ι ε : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε]
  [ESeminormedAddCommMonoid ε]

/-- **Distribution of a finite sum**: `|{|g_1 + ⋯ + g_n| > t}| ≤ ∑ᵢ |{|gᵢ| > t / n}|`, where
`n = s.card`. -/
theorem distribution_sum_le (s : Finset ι) (g : ι → α → ε) (t : ℝ≥0∞) :
    distribution (∑ i ∈ s, g i) t μ ≤ ∑ i ∈ s, distribution (g i) (t / s.card) μ := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [distribution]
  have hn0 : (s.card : ℝ≥0∞) ≠ 0 := by simpa using hs.card_pos.ne'
  have hnt : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold distribution
  calc μ {x | t < ‖(∑ i ∈ s, g i) x‖ₑ}
      ≤ μ (⋃ i ∈ s, {x | t / s.card < ‖g i x‖ₑ}) := by
        refine measure_mono fun x hx => ?_
        simp only [mem_ofPred_eq, Finset.sum_apply] at hx
        simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
        by_contra hcon
        push Not at hcon
        have h1 : ∑ i ∈ s, ‖g i x‖ₑ ≤ s.card • (t / s.card) :=
          Finset.sum_le_card_nsmul s _ _ (fun i hi => hcon i hi)
        rw [nsmul_eq_mul, ENNReal.mul_div_cancel hn0 hnt] at h1
        exact absurd (hx.trans_le ((enorm_sum_le s _).trans h1)) (lt_irrefl _)
    _ ≤ ∑ i ∈ s, μ {x | t / s.card < ‖g i x‖ₑ} := measure_biUnion_finset_le s _

/-- Measure form of `distribution_sum_le`: `|{|g_1 + ⋯ + g_n| > t}| ≤ ∑ᵢ |{|gᵢ| > t / n}|`. -/
theorem measure_enorm_sum_gt_le (s : Finset ι) (g : ι → α → ε) (t : ℝ≥0∞) :
    μ {x | t < ‖∑ i ∈ s, g i x‖ₑ} ≤ ∑ i ∈ s, μ {x | t / s.card < ‖g i x‖ₑ} := by
  have := distribution_sum_le (μ := μ) s g t
  simpa [distribution, superlevelSet, Finset.sum_apply] using this

end Distribution

section Real

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} [SeminormedAddCommGroup E]

/-- Real-level form of `distribution_sum_le` for a seminormed group: for `l ≥ 0`,
`|{‖g_1 + ⋯ + g_n‖ > l}| ≤ ∑ᵢ |{‖gᵢ‖ > l / n}|`. -/
theorem measure_norm_sum_gt_le (s : Finset ι) (g : ι → α → E) {l : ℝ} (hl : 0 ≤ l) :
    μ {x | l < ‖∑ i ∈ s, g i x‖} ≤ ∑ i ∈ s, μ {x | l / s.card < ‖g i x‖} := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [not_lt.2 hl]
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have key := measure_enorm_sum_gt_le (μ := μ) s g (ENNReal.ofReal l)
  have h1 : ∀ (z : E) (m : ℝ), 0 ≤ m → (ENNReal.ofReal m < ‖z‖ₑ ↔ m < ‖z‖) := by
    intro z m hm
    rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff']
    exact ⟨fun h => h.1, fun h => ⟨h, hm.trans_lt h⟩⟩
  have h2 : ENNReal.ofReal l / (s.card : ℝ≥0∞) = ENNReal.ofReal (l / s.card) := by
    rw [ENNReal.ofReal_div_of_pos hn]
    simp
  have e1 : {x | ENNReal.ofReal l < ‖∑ i ∈ s, g i x‖ₑ} = {x | l < ‖∑ i ∈ s, g i x‖} := by
    ext x; exact h1 _ _ hl
  have e2 : ∀ i, {x | ENNReal.ofReal l / (s.card : ℝ≥0∞) < ‖g i x‖ₑ} =
      {x | l / s.card < ‖g i x‖} := by
    intro i
    ext x
    simp only [mem_ofPred_eq, h2]
    exact h1 _ _ (div_nonneg hl hn.le)
  rw [e1] at key
  simpa only [e2] using key

end Real

section Weak

variable {α ι ε : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε]
  [ESeminormedAddCommMonoid ε] [ContinuousAdd ε]

end Weak

end PrimeCarleson.Proof.Common
