module

public import PrimeCarleson.Proof.Oplus.External.THCalderon

/-!
# The Calderón–Zygmund good function

Source: Grafakos–Tao–Terwilleger, L789–L1231 (see L805-L880). For `f` with `|f| ≤ 1_F` and
`f₀ = f 1_{3 I_T}`, `czGood` is the good function `g`: `g = f₀` off `Ω_λ` and `g = ⨍_J f₀` on each
`J ∈ czFam`.

* `czGood_of_mem`, `czGood_of_notMem`: the two defining cases;
* `norm_czAvg_le`: `|⨍_J f₀| ≤ 3λ` for every `J ∈ czFam` (needs the good point `x₀`);
* `norm_czGood_le_ae`: `|g| ≤ 3λ` almost everywhere;
* `czGood_eq_zero_of_notMem_dilate`: `g` is supported in `3 I_T`;
* `aestronglyMeasurable_czGood`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The near part `f₀ = f 1_{3 I_T}`. -/
def nearPart (IT : Dyadic) (f : ℝ → ℂ) : ℝ → ℂ := (IT.dilate 3).indicator f

/-- The average of `f₀` over `J`. -/
def czAvg (IT : Dyadic) (f : ℝ → ℂ) (J : Dyadic) : ℂ :=
  ⨍ z in J.toSet, nearPart IT f z ∂volume

open Classical in
/-- The good function of the Calderón–Zygmund decomposition: `f₀` off `Ω_λ`, the average of `f₀`
over `J` on each `J ∈ czFam`. -/
def czGood (F : Set ℝ) (lam : ℝ) (IT : Dyadic) (f : ℝ → ℂ) : ℝ → ℂ := fun y =>
  if h : ∃ J ∈ czFam F lam IT, y ∈ J.toSet then czAvg IT f (Classical.choose h)
  else nearPart IT f y

variable {F : Set ℝ} {lam : ℝ} {IT : Dyadic} {f : ℝ → ℂ}

/-- On `J ∈ czFam` the good function is the average of `f₀` over `J`. -/
theorem czGood_of_mem {J : Dyadic} (hJ : J ∈ czFam F lam IT) {y : ℝ} (hy : y ∈ J.toSet) :
    czGood F lam IT f y = czAvg IT f J := by
  classical
  have h : ∃ J ∈ czFam F lam IT, y ∈ J.toSet := ⟨J, hJ, hy⟩
  unfold czGood
  simp only [h, ↓reduceDIte]
  have hspec := Classical.choose_spec h
  by_cases heq : Classical.choose h = J
  · rw [heq]
  · exact absurd hy (fun hyJ => Set.disjoint_left.1 (czFam_pairwiseDisjoint hspec.1 hJ heq)
      hspec.2 hyJ)

/-- Off all the intervals of `czFam` the good function is `f₀`. -/
theorem czGood_of_forall_notMem {y : ℝ} (h : ∀ J ∈ czFam F lam IT, y ∉ J.toSet) :
    czGood F lam IT f y = nearPart IT f y := by
  classical
  unfold czGood
  have hn : ¬ ∃ J ∈ czFam F lam IT, y ∈ J.toSet := by
    rintro ⟨J, hJ, hy⟩
    exact h J hJ hy
  simp only [hn, ↓reduceDIte]

/-- Off `Ω_λ` the good function is `f₀`. -/
theorem czGood_of_notMem {y : ℝ} (hy : y ∉ maxSuperlevel F lam) :
    czGood F lam IT f y = nearPart IT f y :=
  czGood_of_forall_notMem fun _ hJ hyJ => hy (czFam_subset hJ hyJ)

/-- `f₀` vanishes off `3 I_T`. -/
theorem nearPart_eq_zero {y : ℝ} (hy : y ∉ IT.dilate 3) : nearPart IT f y = 0 := by
  unfold nearPart; exact indicator_of_notMem hy _

/-- `f₀ = f` on `3 I_T`. -/
theorem nearPart_eq {y : ℝ} (hy : y ∈ IT.dilate 3) : nearPart IT f y = f y := by
  unfold nearPart; exact indicator_of_mem hy _

/-- `f₀` is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_nearPart (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (nearPart IT f) volume :=
  hf.indicator measurableSet_Ico

/-- `|f₀| ≤ |f|`. -/
theorem norm_nearPart_le (y : ℝ) : ‖nearPart IT f y‖ ≤ ‖f y‖ := by
  unfold nearPart
  by_cases hy : y ∈ IT.dilate 3
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, norm_zero]; exact norm_nonneg _

/-- The mass of `F` in a Calderón–Zygmund interval, in real form. -/
theorem measureReal_inter_czFam_le (hF : MeasurableSet F) (hlam : 0 ≤ lam) {x₀ : ℝ}
    (hx₀ : x₀ ∈ IT.toSet) (hx₀Ω : x₀ ∉ maxSuperlevel F lam) {J : Dyadic}
    (hJ : J ∈ czFam F lam IT) (hJ3 : J.toSet ⊆ IT.dilate 3) :
    (volume (F ∩ J.toSet)).toReal ≤ 3 * lam * J.length := by
  have := volume_inter_czFam_le hF hlam hx₀ hx₀Ω hJ hJ3
  have hJl := J.length_pos
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) this

/-- **`|⨍_J f₀| ≤ 3λ`** for every `J ∈ czFam`. -/
theorem norm_czAvg_le (hF : MeasurableSet F) (hlam : 0 ≤ lam) {x₀ : ℝ} (hx₀ : x₀ ∈ IT.toSet)
    (hx₀Ω : x₀ ∉ maxSuperlevel F lam) (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x)
    {J : Dyadic} (hJ : J ∈ czFam F lam IT) : ‖czAvg IT f J‖ ≤ 3 * lam := by
  have hJl := J.length_pos
  have hfin : volume J.toSet ≠ ⊤ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  by_cases hJ3 : J.toSet ⊆ IT.dilate 3
  · have hmass := measureReal_inter_czFam_le hF hlam hx₀ hx₀Ω hJ hJ3
    unfold czAvg
    rw [setAverage_eq, norm_smul, Dyadic.volume_real_toSet, norm_inv, Real.norm_eq_abs,
      abs_of_pos hJl]
    have h1 : ‖∫ z in J.toSet, nearPart IT f z‖ ≤ (volume (F ∩ J.toSet)).toReal := by
      refine (norm_integral_le_integral_norm _).trans ?_
      have h2 : ∫ z in J.toSet, ‖nearPart IT f z‖ ≤
          ∫ z in J.toSet, F.indicator (fun _ => (1 : ℝ)) z :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
          ((integrable_indicator_iff hF).2 (integrableOn_const (μ := volume.restrict J.toSet)
            (s := F) (C := (1 : ℝ)) (by
              rw [Measure.restrict_apply hF]
              exact ne_top_of_le_ne_top hfin (measure_mono inter_subset_right))))
          (Filter.Eventually.of_forall fun z => (norm_nearPart_le z).trans (hf z))
      refine h2.trans (le_of_eq ?_)
      rw [setIntegral_indicator hF, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
        inter_comm]
    calc J.length⁻¹ * ‖∫ z in J.toSet, nearPart IT f z‖ ≤ J.length⁻¹ * (3 * lam * J.length) :=
          mul_le_mul_of_nonneg_left (h1.trans hmass) (by positivity)
      _ = 3 * lam := by field_simp
  · -- `J` misses `3 I_T`, so `f₀ = 0` on `J`
    have hmiss : ∀ y ∈ J.toSet, y ∉ IT.dilate 3 := by
      intro y hy hy3
      exact hJ3 (subset_dilate_three_of_meets (czFam_k_le hJ) ⟨y, hy, hy3⟩)
    have : czAvg IT f J = 0 := by
      unfold czAvg
      rw [setAverage_congr_fun J.measurableSet_toSet
        (Filter.Eventually.of_forall fun y hy => nearPart_eq_zero (hmiss y hy))]
      simp
    rw [this, norm_zero]; linarith

/-- A Calderón–Zygmund interval not inside `3 I_T` misses `3 I_T`, so `⨍_J f₀ = 0`. -/
theorem czAvg_eq_zero {J : Dyadic} (hJ : J ∈ czFam F lam IT) (hJ3 : ¬ J.toSet ⊆ IT.dilate 3) :
    czAvg IT f J = 0 := by
  have hmiss : ∀ y ∈ J.toSet, y ∉ IT.dilate 3 := by
    intro y hy hy3
    exact hJ3 (subset_dilate_three_of_meets (czFam_k_le hJ) ⟨y, hy, hy3⟩)
  unfold czAvg
  rw [setAverage_congr_fun J.measurableSet_toSet
    (Filter.Eventually.of_forall fun y hy => nearPart_eq_zero (hmiss y hy))]
  simp

/-- The good function vanishes off `3 I_T`. -/
theorem czGood_eq_zero_of_notMem_dilate {y : ℝ} (hy : y ∉ IT.dilate 3) :
    czGood F lam IT f y = 0 := by
  by_cases h : ∃ J ∈ czFam F lam IT, y ∈ J.toSet
  · obtain ⟨J, hJ, hyJ⟩ := h
    rw [czGood_of_mem hJ hyJ]
    have hmiss : ∀ z ∈ J.toSet, z ∉ IT.dilate 3 := by
      intro z hz hz3
      have := subset_dilate_three_of_meets (czFam_k_le hJ) ⟨z, hz, hz3⟩
      exact hy (this hyJ)
    unfold czAvg
    rw [setAverage_congr_fun J.measurableSet_toSet
      (Filter.Eventually.of_forall fun z hz => nearPart_eq_zero (hmiss z hz))]
    simp
  · push Not at h
    rw [czGood_of_forall_notMem h, nearPart_eq_zero hy]

/-- **`|g| ≤ 3λ` almost everywhere.** -/
theorem norm_czGood_le_ae (hF : MeasurableSet F) (hlam : 0 < lam) {x₀ : ℝ}
    (hx₀ : x₀ ∈ IT.toSet) (hx₀Ω : x₀ ∉ maxSuperlevel F lam)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) :
    ∀ᵐ y : ℝ, ‖czGood F lam IT f y‖ ≤ 3 * lam := by
  have hoff : ∀ᵐ y : ℝ, y ∉ maxSuperlevel F lam → ‖nearPart IT f y‖ ≤ lam := by
    by_cases hl1 : lam < 1
    · filter_upwards [ae_mem_maxSuperlevel_of_mem hF hl1] with y hy hyΩ
      have hyF : y ∉ F := fun h => hyΩ (hy h)
      have := hf y
      rw [indicator_of_notMem hyF] at this
      exact (norm_nearPart_le y).trans (this.trans hlam.le)
    · refine Filter.Eventually.of_forall fun y _ => ?_
      have h1 := hf y
      have : F.indicator (fun _ => (1 : ℝ)) y ≤ 1 := by
        by_cases hy : y ∈ F <;> simp [hy]
      exact (norm_nearPart_le y).trans (h1.trans (this.trans (not_lt.1 hl1)))
  filter_upwards [hoff] with y hy
  by_cases hyΩ : y ∈ maxSuperlevel F lam
  · obtain ⟨J, hJ, hyJ⟩ := exists_czFam_mem_of_mem (IT := IT) hyΩ
    rw [czGood_of_mem hJ hyJ]
    exact norm_czAvg_le hF hlam.le hx₀ hx₀Ω hf hJ
  · rw [czGood_of_notMem hyΩ]
    linarith [hy hyΩ]

/-- The good function is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_czGood (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (czGood F lam IT f) volume := by
  rw [← Measure.restrict_univ (μ := volume),
    ← union_compl_self (⋃ J : czFam F lam IT, (J : Dyadic).toSet), aestronglyMeasurable_union_iff]
  constructor
  · rw [aestronglyMeasurable_iUnion_iff]
    intro J
    have : czGood F lam IT f =ᵐ[volume.restrict (J : Dyadic).toSet]
        fun _ => czAvg IT f (J : Dyadic) :=
      (ae_restrict_iff' (J : Dyadic).measurableSet_toSet).2
        (Filter.Eventually.of_forall fun y hy => czGood_of_mem J.2 hy)
    exact aestronglyMeasurable_const.congr this.symm
  · have : czGood F lam IT f =ᵐ[volume.restrict (⋃ J : czFam F lam IT, (J : Dyadic).toSet)ᶜ]
        nearPart IT f := by
      filter_upwards [ae_restrict_mem
        (MeasurableSet.iUnion fun J : czFam F lam IT => (J : Dyadic).measurableSet_toSet).compl]
        with y hy
      exact czGood_of_forall_notMem fun J hJ hyJ => hy (mem_iUnion.2 ⟨⟨J, hJ⟩, hyJ⟩)
    exact ((aestronglyMeasurable_nearPart hf).mono_measure Measure.restrict_le_self).congr this.symm

end PrimeCarleson.Proof.Oplus
