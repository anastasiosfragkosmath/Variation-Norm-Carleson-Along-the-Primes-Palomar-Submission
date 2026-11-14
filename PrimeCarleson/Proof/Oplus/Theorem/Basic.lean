module

public import PrimeCarleson.Proof.Oplus.Decomposition.WavePacketRep

/-!
# Continuity of `𝒮[f]` and the pointwise bound for `𝒮'` ([O+] L894-L896, L905-L916)

Source: [O+], L894–L896 and L905-L916 (the linearizing data):

* `continuous_partialFourierIntegral_prod`: for a Schwartz function `f` the map
  `(ξ, x) ↦ 𝒮[f](ξ, x)` is continuous on `ℝ²` ("depends continuously on `(ξ, x)`");
* `Linearization.measurable_op`: the linearized operator `𝒮'[f]` is measurable (this is what the
  measurability of `x ↦ ξ_k(x)` and the joint continuity give);
* `Linearization.norm_op_sub_op_le`: `|𝒮'[f](x) - 𝒮'[g](x)| ≤ K ‖f̂ - ĝ‖_{L¹}` for every `x`
  (the increments of `𝒮[f]` over an interval are bounded by `‖f̂‖_{L¹}` and `|a_k| ≤ 1`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- The Fourier transform of a Schwartz function is integrable. -/
theorem integrable_fourier_schwartz (f : 𝓢(ℝ, ℂ)) : Integrable (𝓕 (⇑f)) := by
  have h1 : Integrable (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := (𝓕 f : 𝓢(ℝ, ℂ)).integrable
  rwa [SchwartzMap.fourier_coe] at h1

/-- **Continuity of `𝒮[f]`** ([O+] L894-L896): for a
Schwartz function `f`, `(ξ, x) ↦ 𝒮[f](ξ, x)` is continuous on `ℝ × ℝ`. -/
theorem continuous_partialFourierIntegral_prod (f : 𝓢(ℝ, ℂ)) :
    Continuous fun p : ℝ × ℝ => partialFourierIntegral f p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p₀
  have hint := integrable_fourier_schwartz f
  have hfun : (fun p : ℝ × ℝ => partialFourierIntegral f p.1 p.2) =
      fun p => ∫ η, (Iic p.1).indicator (fun η => 𝓕 (⇑f) η * e (η * p.2)) η := by
    funext p
    rw [partialFourierIntegral_eq, integral_indicator measurableSet_Iic]
  rw [hfun]
  refine continuousAt_of_dominated (bound := fun η => ‖𝓕 (⇑f) η‖) ?_ ?_ hint.norm ?_
  · exact Eventually.of_forall fun p =>
      (integrable_fourier_mul_e f p.2).aestronglyMeasurable.indicator measurableSet_Iic
  · refine Eventually.of_forall fun p => Eventually.of_forall fun η => ?_
    refine (norm_indicator_le_norm_self _ _).trans ?_
    rw [norm_mul, norm_e, mul_one]
  · have hne : ∀ᵐ η ∂(volume : Measure ℝ), η ∉ ({p₀.1} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem _
    filter_upwards [hne] with η hη
    have hη' : η ≠ p₀.1 := hη
    have hcont : Continuous fun p : ℝ × ℝ => 𝓕 (⇑f) η * e (η * p.2) :=
      continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_snd))
    rcases lt_or_gt_of_ne hη' with h | h
    · refine hcont.continuousAt.congr ?_
      have : ∀ᶠ p : ℝ × ℝ in 𝓝 p₀, η < p.1 :=
        (continuous_fst.continuousAt.eventually (lt_mem_nhds h))
      filter_upwards [this] with p hp
      simp [Set.indicator_of_mem (show η ∈ Iic p.1 from le_of_lt hp)]
    · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      have : ∀ᶠ p : ℝ × ℝ in 𝓝 p₀, p.1 < η :=
        (continuous_fst.continuousAt.eventually (gt_mem_nhds h))
      filter_upwards [this] with p hp
      simp [Set.indicator_of_notMem (show η ∉ Iic p.1 from not_le.2 hp)]

/-- **`𝒮'[f]` is measurable.** -/
theorem Linearization.measurable_op {r : ℝ} (L : Linearization r) (f : 𝓢(ℝ, ℂ)) :
    Measurable (L.op f) := by
  have hS := (continuous_partialFourierIntegral_prod f).measurable
  unfold Linearization.op
  refine Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.mul (Measurable.sub ?_ ?_) (L.measurable_a k)
  · exact hS.comp ((L.measurable_ξ k.succ).prodMk measurable_id)
  · exact hS.comp ((L.measurable_ξ k.castSucc).prodMk measurable_id)

/-- The increments of `𝒮[f] - 𝒮[g]` over an interval are bounded by `‖f̂ - ĝ‖_{L¹}`. -/
theorem norm_partialFourierIntegral_sub_sub_le (f g : 𝓢(ℝ, ℂ)) {ξ ξ' : ℝ} (h : ξ ≤ ξ') (x : ℝ) :
    ‖(partialFourierIntegral f ξ' x - partialFourierIntegral f ξ x) -
        (partialFourierIntegral g ξ' x - partialFourierIntegral g ξ x)‖ ≤
      ∫ η, ‖𝓕 (⇑f) η - 𝓕 (⇑g) η‖ := by
  rw [partialFourierIntegral_sub_eq_intervalIntegral,
    partialFourierIntegral_sub_eq_intervalIntegral,
    ← intervalIntegral.integral_sub (integrable_fourier_mul_e f x).intervalIntegrable
      (integrable_fourier_mul_e g x).intervalIntegrable]
  refine (intervalIntegral.norm_integral_le_integral_norm h).trans ?_
  rw [intervalIntegral.integral_of_le h]
  have hint : Integrable (fun η => ‖𝓕 (⇑f) η - 𝓕 (⇑g) η‖) :=
    ((integrable_fourier_schwartz f).sub (integrable_fourier_schwartz g)).norm
  have hnorm : ∀ η, ‖𝓕 (⇑f) η * e (η * x) - 𝓕 (⇑g) η * e (η * x)‖ =
      ‖𝓕 (⇑f) η - 𝓕 (⇑g) η‖ := fun η => by rw [← sub_mul, norm_mul, norm_e, mul_one]
  simp_rw [hnorm]
  exact setIntegral_le_integral hint (Eventually.of_forall fun η => norm_nonneg _)

/-- **`|𝒮'[f](x) - 𝒮'[g](x)| ≤ K ‖f̂ - ĝ‖_{L¹}`** for every `x`, `r > 1` (the coefficients satisfy
`|a_k| ≤ 1`). -/
theorem Linearization.norm_op_sub_op_le {r : ℝ} (hr : 1 < r) (L : Linearization r)
    (f g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖L.op f x - L.op g x‖ ≤ L.K * ∫ η, ‖𝓕 (⇑f) η - 𝓕 (⇑g) η‖ := by
  unfold Linearization.op
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k : Fin L.K, ‖(partialFourierIntegral f (L.ξ k.succ x) x -
          partialFourierIntegral f (L.ξ k.castSucc x) x) * L.a k x -
        (partialFourierIntegral g (L.ξ k.succ x) x -
          partialFourierIntegral g (L.ξ k.castSucc x) x) * L.a k x‖
      ≤ ∑ _k : Fin L.K, ∫ η, ‖𝓕 (⇑f) η - 𝓕 (⇑g) η‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← sub_mul, norm_mul]
        calc _ ≤ (∫ η, ‖𝓕 (⇑f) η - 𝓕 (⇑g) η‖) * 1 := by
              gcongr
              · exact (norm_partialFourierIntegral_sub_sub_le f g (L.ξ_castSucc_lt k x).le x)
              · exact L.norm_a_le_one hr k x
          _ = _ := mul_one _
    _ = L.K * ∫ η, ‖𝓕 (⇑f) η - 𝓕 (⇑g) η‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end PrimeCarleson.Proof.Oplus
