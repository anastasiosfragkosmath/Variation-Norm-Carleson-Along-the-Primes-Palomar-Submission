module

public import PrimeCarleson.Proof.MswTransference.Cutoff
public import PrimeCarleson.Proof.MswTransference.Schur
public import PrimeCarleson.Proof.MswTransference.Variation

/-!
# Sampling and synthesis bounds

The two halves of [MSW] Lemma 2.1 ([MSW] L371–L458), with the Schwartz cutoff `Φ = cutoff` in
place of the Fejér kernel and the constant `A₁ = cutoffConst`:

* `eLpNorm_rVariationOn_sample_le` (Source: [MSW], L371–L379): if every `H t`
  reproduces under convolution with `Φ` at the integers, then
  `‖V^r(H_t(n))‖_{ℓ^p(ℤ)} ≤ A₁ ‖V^r(H_t(x))‖_{L^p(ℝ)}`;
* `eLpNorm_extend_le` (Source: [MSW], L371–L379):
  `‖Σₖ f(k) Φ(· - k)‖_{L^p(ℝ)} ≤ A₁ ‖f‖_{ℓ^p(ℤ)}`.

Both are the Schur test (`eLpNorm_le_of_le_lintegral_kernel_of_aemeasurable`) for the kernel
`|Φ(x - y)|` between `ℤ` and `ℝ`, whose row and column integrals are at most `A₁`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.MswTransference

/-- `∫ |Φ(a - y)| dy ≤ A₁`. -/
theorem lintegral_enorm_cutoff_sub_le (a : ℝ) :
    ∫⁻ y, ‖cutoff (a - y)‖ₑ ≤ cutoffConst := by
  rw [lintegral_sub_left_eq_self (fun y => ‖cutoff y‖ₑ) a]
  exact le_max_left _ _

/-- `∑ₙ |Φ(x + n)| ≤ A₁`. -/
theorem tsum_enorm_cutoff_add_le (x : ℝ) :
    ∑' n : ℤ, ‖cutoff (x + n)‖ₑ ≤ cutoffConst :=
  (le_iSup (fun x : ℝ => ∑' n : ℤ, ‖cutoff (x + n)‖ₑ) x).trans (le_max_right _ _)

/-- `∑ₙ |Φ(x - n)| ≤ A₁`. -/
theorem tsum_enorm_cutoff_sub_le (x : ℝ) :
    ∑' n : ℤ, ‖cutoff (x - n)‖ₑ ≤ cutoffConst := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  simpa [sub_eq_add_neg] using tsum_enorm_cutoff_add_le x

/-- Sampling bound ([MSW] Lemma 2.1, converse half, for the `V^r` seminorm). -/
theorem eLpNorm_rVariationOn_sample_le {r : ℝ} (hr : 1 ≤ r) {p : ℝ} (hp : 1 ≤ p) (T : Finset ℝ)
    (H : ℝ → ℝ → ℂ) (hcont : ∀ t ∈ T, Continuous (H t))
    (hint : ∀ t ∈ T, ∀ x : ℝ, Integrable (fun y => H t y * cutoff (x - y)))
    (hrep : ∀ t ∈ T, ∀ n : ℤ, H t n = ∫ y, H t y * cutoff (n - y)) :
    eLpNorm (fun n : ℤ => rVariationOn r T (fun t => H t n)) (ENNReal.ofReal p) Measure.count ≤
      cutoffConst * eLpNorm (fun x => rVariationOn r T (fun t => H t x)) (ENNReal.ofReal p)
        volume := by
  refine eLpNorm_le_of_le_lintegral_kernel_of_aemeasurable (μ := Measure.count)
    (K := fun (n : ℤ) (y : ℝ) => ‖cutoff (n - y)‖ₑ) ?_
    (measurable_rVariationOn hr fun t ht => hcont t (Finset.mem_coe.1 ht))
    (fun n => lintegral_enorm_cutoff_sub_le n) ?_ (measurable_of_countable _).aemeasurable ?_ hp
  · exact (by fun_prop : Continuous fun q : ℤ × ℝ => ‖cutoff (q.1 - q.2)‖ₑ).measurable
  · intro y
    rw [lintegral_count]
    simpa [sub_eq_neg_add] using tsum_enorm_cutoff_add_le (-y)
  · intro n
    calc rVariationOn r T (fun t => H t n)
        = rVariationOn r T (fun t => ∫ y, H t y * cutoff (n - y)) :=
          rVariationOn_congr fun t ht => hrep t (Finset.mem_coe.1 ht) n
      _ ≤ ∫⁻ y, rVariationOn r T (fun t => H t y) * ‖cutoff (n - y)‖ₑ :=
          rVariationOn_integral_le hr H (fun y => cutoff (n - y))
            fun t ht => hint t (Finset.mem_coe.1 ht) n
      _ = ∫⁻ y, ‖cutoff (n - y)‖ₑ * rVariationOn r T (fun t => H t y) := by
          simp_rw [mul_comm]

/-- Synthesis bound ([MSW] Lemma 2.1, upper half, with the Schwartz cutoff). -/
theorem eLpNorm_extend_le {p : ℝ} (hp : 1 ≤ p) (f : ℤ →₀ ℂ) :
    eLpNorm (⇑(extend f)) (ENNReal.ofReal p) volume ≤
      cutoffConst * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  rw [← eLpNorm_enorm (⇑(extend f)) (extend f).continuous.aestronglyMeasurable,
    ← eLpNorm_enorm (⇑f) (measurable_of_countable (⇑f)).aestronglyMeasurable]
  refine eLpNorm_le_of_le_lintegral_kernel_of_aemeasurable (ν := Measure.count)
    (K := fun (x : ℝ) (k : ℤ) => ‖cutoff (x - k)‖ₑ) ?_ (measurable_of_countable _) ?_ ?_
    (extend f).continuous.enorm.aemeasurable ?_ hp
  · exact (by fun_prop : Continuous fun q : ℝ × ℤ => ‖cutoff (q.1 - q.2)‖ₑ).measurable
  · intro x
    rw [lintegral_count]
    exact tsum_enorm_cutoff_sub_le x
  · intro k
    rw [lintegral_sub_right_eq_self (fun y => ‖cutoff y‖ₑ) (k : ℝ)]
    exact le_max_left _ _
  · intro x
    rw [lintegral_count, extend_apply, Finsupp.sum]
    calc ‖∑ k ∈ f.support, f k * cutoff (x - k)‖ₑ
        ≤ ∑ k ∈ f.support, ‖f k * cutoff (x - k)‖ₑ := enorm_sum_le _ _
      _ = ∑ k ∈ f.support, ‖cutoff (x - k)‖ₑ * ‖f k‖ₑ := by
          simp_rw [enorm_mul, mul_comm]
      _ ≤ ∑' k : ℤ, ‖cutoff (x - k)‖ₑ * ‖f k‖ₑ := ENNReal.sum_le_tsum _

end PrimeCarleson.Proof.MswTransference
