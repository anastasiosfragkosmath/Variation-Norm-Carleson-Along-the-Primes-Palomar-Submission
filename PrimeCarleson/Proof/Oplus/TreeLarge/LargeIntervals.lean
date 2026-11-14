module

public import PrimeCarleson.Proof.Oplus.TreeLarge.Overlapping
public import PrimeCarleson.Proof.Oplus.TreeSmall.AwayFromTop

/-!
# The large-interval estimate for `l`-lacunary and `l`-overlapping trees ([O+] L2144-L2442)

Source: [O+] `treeestimatelargeintervals`, L2144–L2152 (display (treeestimatelargeintervals)):
for a tree `T` which is `l`-lacunary, or
`l`-overlapping with (jconsolidation) and `l⁺` or `l⁻`, and `1 ≤ q ≤ 2`,
`(∑_{J ∈ 𝒥, J ∩ 16 I_T ≠ ∅} ‖∑_{P ∈ T : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q(J)}^q)^{1/q}
≲ ene den^{min(1, r'/q)} |I_T|^{1/q}`
(L2250-L2252 reads the display this way; the printed `L^q(16 I_T)` norm of a `J`-dependent sum
is the sum over `J`).

* `holder_lintegral_rpow`: Hölder on a set, `∫_U h^q ≤ (∫_U h^p)^{q/p} |U|^{1-q/p}` for `q ≤ p`;
* `large_intervals_sum_ge` (`q ≥ r'`): `lacunary_case_sum` (`TreeSmall/Lacunary.lean`) and
  `overlapping_case_sum`;
* `treeestimate_large_intervals_sum` (all `1 ≤ q ≤ 2`): for `q < r'` Hölder on `J` and on the sum
  over `J` (the source: "Again, by Hölder's inequality, we may assume `q ≥ r'`", L2151, "for
  `q < r'` pass from `q = r'` as in the small-interval estimate"), giving the factor
  `den^{min(1, r'/q)}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- **Hölder on a set**: for `0 < q ≤ p` and measurable `h`,
`∫_U h^q ≤ (∫_U h^p)^{q/p} |U|^{1 - q/p}`. -/
theorem holder_lintegral_rpow {q p : ℝ} (hq0 : 0 < q) (hqp : q ≤ p) {h : ℝ → ℝ≥0∞}
    (hh : Measurable h) (U : Set ℝ) :
    ∫⁻ x in U, h x ^ q ≤ (∫⁻ x in U, h x ^ p) ^ (q / p) * volume U ^ (1 - q / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le hq0 hqp
  have hmeasU : AEStronglyMeasurable h (volume.restrict U) := hh.aestronglyMeasurable
  have hle : ENNReal.ofReal q ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hqp
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict U) hle hmeasU
  have hnorm : ∀ s : ℝ, 0 < s → eLpNorm h (ENNReal.ofReal s) (volume.restrict U) =
      (∫⁻ x in U, h x ^ s) ^ (1 / s) := by
    intro s hs
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hs).ne'
      ENNReal.ofReal_ne_top hmeasU, ENNReal.toReal_ofReal hs.le]
    simp only [enorm_eq_self]
  have hpow : ∀ s : ℝ, 0 < s → ∫⁻ x in U, h x ^ s =
      eLpNorm h (ENNReal.ofReal s) (volume.restrict U) ^ s := by
    intro s hs
    rw [hnorm s hs, ← ENNReal.rpow_mul, one_div_mul_cancel hs.ne', ENNReal.rpow_one]
  rw [Measure.restrict_apply_univ] at hH
  rw [ENNReal.toReal_ofReal hq0.le, ENNReal.toReal_ofReal hp0.le] at hH
  calc ∫⁻ x in U, h x ^ q = eLpNorm h (ENNReal.ofReal q) (volume.restrict U) ^ q := hpow q hq0
    _ ≤ (eLpNorm h (ENNReal.ofReal p) (volume.restrict U) * volume U ^ (1 / q - 1 / p)) ^ q :=
        ENNReal.rpow_le_rpow hH hq0.le
    _ = (∫⁻ x in U, h x ^ p) ^ (q / p) * volume U ^ (1 - q / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, hnorm p hp0,
          ← ENNReal.rpow_mul]
        congr 2
        · field_simp
        · field_simp

section Large

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ}

/-- The trees treated in the proof of the tree estimate: `l`-lacunary, or `l`-overlapping with
(jconsolidation) (one integer `j`) and `l⁺` or `l⁻`. -/
def MultitileTree.IsSpecialJ (C₂ : ℝ) (𝒯 : MultitileTree ρ) : Prop :=
  𝒯.IsLacunary C₂ ∨ (𝒯.IsOverlapping C₂ ∧ (𝒯.IsPlus ∨ 𝒯.IsMinus) ∧
    ∃ j : ℤ, ∀ P ∈ 𝒯.T, 𝒯.ξ - j * P.ωu.length ∈ P.ωl)


/-- **The large-interval estimate for special trees, `q ≥ r'`**: `lacunary_case_sum`
(`TreeSmall/Lacunary.lean`) and `overlapping_case_sum`. -/
theorem large_intervals_sum_ge {r q : ℝ} (hr : 2 < r) (hq : Real.conjExponent r ≤ q)
    (hq2 : q ≤ 2) {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → 𝒯.IsSpecialJ C₂ → 𝒯.T.Nonempty →
      ∀ (𝒥s : Finset Dyadic), (∀ J ∈ 𝒥s, 𝒯.IsMaxAvoiding J ∧
        (J.toSet ∩ 𝒯.I.dilate 16).Nonempty) →
        ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤
            P.I.length) x‖ₑ ^ q ≤
          ENNReal.ofReal (K * ene ^ q * den ^ Real.conjExponent r * (48 * 𝒯.I.length)) := by
  have hr1 : 1 < r := by linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := lacunary_case_sum (r := r) (q := q) hr1 hq
  obtain ⟨K₂, hK₂0, hK₂⟩ := overlapping_case_sum hr hq hq2 hC
  refine ⟨max K₁ K₂, le_max_of_le_left hK₁0, ?_⟩
  intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep hspec hne 𝒥s h𝒥
  have hnn : 0 ≤ ene ^ q * den ^ Real.conjExponent r * (48 * 𝒯.I.length) := by
    have := 𝒯.I.length_pos
    positivity
  rcases hspec with hlac | ⟨hov, hpm, hjc⟩
  · refine (hK₁ hC hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hlac hsep hne 𝒥s h𝒥).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [le_max_left K₁ K₂]
  · refine (hK₂ hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hov hpm hjc hsep hne 𝒥s h𝒥).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [le_max_right K₁ K₂]

/-- Real bookkeeping for the Hölder step in `q < r'`. -/
theorem rpow_bookkeeping_holder {q p K₀ e d W : ℝ} (hp : 0 < p)
    (hK : 0 ≤ K₀) (he : 0 ≤ e) (hd : 0 ≤ d) (hW : 0 < W) :
    (K₀ * e ^ p * d ^ p * W) ^ (q / p) * W ^ (1 - q / p) = (K₀ ^ (1 / p) * e * d) ^ q * W := by
  have h1 : (K₀ * e ^ p * d ^ p * W) ^ (q / p) =
      K₀ ^ (q / p) * e ^ q * d ^ q * W ^ (q / p) := by
    rw [Real.mul_rpow (by positivity) hW.le, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hK (by positivity), ← Real.rpow_mul he, ← Real.rpow_mul hd]
    congr 3 <;> (rw [mul_div_cancel₀ _ hp.ne'])
  have h2 : (K₀ ^ (1 / p) * e * d) ^ q = K₀ ^ (q / p) * e ^ q * d ^ q := by
    rw [Real.mul_rpow (by positivity) hd, Real.mul_rpow (by positivity) he,
      ← Real.rpow_mul hK, one_div_mul_eq_div]
  have h3 : W ^ (q / p) * W ^ (1 - q / p) = W := by
    rw [← Real.rpow_add hW]
    norm_num
  rw [h1, h2]
  calc K₀ ^ (q / p) * e ^ q * d ^ q * W ^ (q / p) * W ^ (1 - q / p)
      = K₀ ^ (q / p) * e ^ q * d ^ q * (W ^ (q / p) * W ^ (1 - q / p)) := by ring
    _ = _ := by rw [h3]


open Classical in
/-- **`treeestimatelargeintervals`** for special trees and all `1 ≤ q ≤ 2`
([O+] L2144-L2152, read as in L2250-L2252): for an `l`-lacunary tree, or an `l`-overlapping tree
with (jconsolidation) and `l^±`, and every finite set `𝒥s` of elements of `𝒥` meeting `16 I_T`,
`∑_{J ∈ 𝒥s} ∫_J |∑_{P ∈ T : |I| ≥ C''|J|} ⟨f, φ_P⟩ φ_P a_P 1_E|^q ≤
(K ene den^{min(1, r'/q)})^q 48 |I_T|`. For `q < r'` this is Hölder from `q = r'`. -/
theorem treeestimate_large_intervals_sum {r q : ℝ} (hr : 2 < r) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    {C₁ C₂ C₃ : ℝ} (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) → 𝒯.IsSpecialJ C₂ → 𝒯.T.Nonempty →
      ∀ (𝒥s : Finset Dyadic), (∀ J ∈ 𝒥s, 𝒯.IsMaxAvoiding J ∧
        (J.toSet ∩ 𝒯.I.dilate 16).Nonempty) →
        ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖treeSum ch f L E (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤
            P.I.length) x‖ₑ ^ q ≤
          ENNReal.ofReal ((K * ene * den ^ (min 1 (Real.conjExponent r / q))) ^ q *
            (48 * 𝒯.I.length)) := by
  have hr1 : 1 < r := by linarith
  have hr' : 0 < Real.conjExponent r := by
    unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  have hr'2 : Real.conjExponent r ≤ 2 := by
    unfold Real.conjExponent
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hq0 : 0 < q := by linarith
  by_cases hqr : Real.conjExponent r ≤ q
  · obtain ⟨K₀, hK₀, hK⟩ := large_intervals_sum_ge hr hqr hq2 hC
    refine ⟨K₀ ^ (1 / q), by positivity, ?_⟩
    intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep hspec hne 𝒥s h𝒥
    refine (hK hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep hspec hne 𝒥s h𝒥).trans ?_
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hmin : min 1 (Real.conjExponent r / q) = Real.conjExponent r / q :=
      min_eq_right (by rw [div_le_one hq0]; exact hqr)
    rw [hmin, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), ← Real.rpow_mul hK₀, one_div_mul_cancel hq0.ne', Real.rpow_one,
      ← Real.rpow_mul hden, div_mul_cancel₀ _ hq0.ne']
  · rw [not_le] at hqr
    obtain ⟨K₀, hK₀, hK⟩ := large_intervals_sum_ge hr (le_refl (Real.conjExponent r)) hr'2 hC
    refine ⟨K₀ ^ (1 / Real.conjExponent r), by positivity, ?_⟩
    intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep hspec hne 𝒥s h𝒥
    have hmin : min 1 (Real.conjExponent r / q) = 1 :=
      min_eq_left (by rw [le_div_iff₀ hq0]; linarith)
    rw [hmin, Real.rpow_one]
    have hWpos : 0 < 48 * 𝒯.I.length := by have := 𝒯.I.length_pos; positivity
    set Fn : Dyadic → ℝ → ℂ := fun J => treeSum ch f L E
      (𝒯.T.filter fun P => Cpp C₁ C₂ * J.length ≤ P.I.length) with hFn
    set F : ℝ → ℂ := fun x => ∑ J ∈ 𝒥s, J.toSet.indicator (Fn J) x with hF
    have hdisj : (𝒥s : Set Dyadic).PairwiseDisjoint Dyadic.toSet := fun J hJ J' hJ' hne' =>
      (h𝒥 J hJ).1.disjoint (h𝒥 J' hJ').1 hne'
    have hFm : Measurable F :=
      Finset.measurable_sum _ fun J _ =>
        (measurable_treeSum ch f L hE _).indicator J.measurableSet_toSet
    have hFJ : ∀ J ∈ 𝒥s, ∀ x ∈ J.toSet, F x = Fn J x := by
      intro J hJ x hx
      rw [hF]
      simp only
      rw [Finset.sum_eq_single J]
      · rw [Set.indicator_of_mem hx]
      · intro J' hJ' hne'
        refine Set.indicator_of_notMem (fun hx' => ?_) _
        exact Set.disjoint_left.1 (hdisj hJ hJ' (Ne.symm hne')) hx hx'
      · intro hJ'; exact absurd hJ hJ'
    have hsum : ∀ s : ℝ, ∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖Fn J x‖ₑ ^ s =
        ∫⁻ x in ⋃ J ∈ 𝒥s, J.toSet, ‖F x‖ₑ ^ s := by
      intro s
      rw [lintegral_biUnion_finset hdisj (fun J _ => J.measurableSet_toSet)]
      refine Finset.sum_congr rfl fun J hJ => ?_
      exact setLIntegral_congr_fun J.measurableSet_toSet (fun x hx => by rw [hFJ J hJ x hx])
    have hvolU : volume (⋃ J ∈ 𝒥s, J.toSet) ≤ ENNReal.ofReal (48 * 𝒯.I.length) := by
      rw [measure_biUnion_finset hdisj (fun J _ => J.measurableSet_toSet)]
      simp_rw [Dyadic.volume_toSet]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun J _ => J.length_pos.le)]
      exact ENNReal.ofReal_le_ofReal (MultitileTree.sum_length_le hne hT.time 𝒥s h𝒥)
    have hge := hK hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep hspec hne 𝒥s h𝒥
    have hHold := holder_lintegral_rpow hq0 hqr.le (h := fun x => ‖F x‖ₑ) hFm.enorm
      (⋃ J ∈ 𝒥s, J.toSet)
    rw [← hsum q] at hHold
    rw [← hsum (Real.conjExponent r)] at hHold
    have hexp : 0 ≤ 1 - q / Real.conjExponent r := by
      rw [sub_nonneg, div_le_one hr']; exact hqr.le
    refine hHold.trans ?_
    calc (∑ J ∈ 𝒥s, ∫⁻ x in J.toSet, ‖Fn J x‖ₑ ^ Real.conjExponent r) ^ (q / Real.conjExponent r) *
          volume (⋃ J ∈ 𝒥s, J.toSet) ^ (1 - q / Real.conjExponent r)
        ≤ (ENNReal.ofReal (K₀ * ene ^ Real.conjExponent r * den ^ Real.conjExponent r *
              (48 * 𝒯.I.length))) ^ (q / Real.conjExponent r) *
            (ENNReal.ofReal (48 * 𝒯.I.length)) ^ (1 - q / Real.conjExponent r) := by
          gcongr
      _ = ENNReal.ofReal ((K₀ * ene ^ Real.conjExponent r * den ^ Real.conjExponent r *
              (48 * 𝒯.I.length)) ^ (q / Real.conjExponent r) *
            (48 * 𝒯.I.length) ^ (1 - q / Real.conjExponent r)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
            ENNReal.ofReal_rpow_of_nonneg hWpos.le hexp, ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((K₀ ^ (1 / Real.conjExponent r) * ene * den) ^ q *
            (48 * 𝒯.I.length)) := by
          rw [rpow_bookkeeping_holder hr' hK₀ hene hden hWpos]

end Large

end PrimeCarleson.Proof.Oplus
