module

public import PrimeCarleson.Proof.Oplus.External.THTerms
public import PrimeCarleson.Proof.Oplus.Estimates.UnivBound
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoGeometry

/-!
# Assembly of the tile-energy bound for abstract packet families

Source: Grafakos–Tao–Terwilleger, L768–L787 and L789–L1231; [O+] `tilessmallmaxprop`,
L2456–L2465.

* `sum_sq_tsum_le_of_forall_finset`: from finite partial sums to `tsum`s for a finite sum of
  squares;
* `sum_length_mul_ratio_pow_le_gen`: counting by scales, `∑_I |I| (|I|/|I_T|)^4 ≤ (4/3)|I_T|`;
* `far_part_sum_le`: `∑_I |⟨f 1_{(3 I_T)ᶜ}, ψ_I⟩|² ≲ A² λ² |I_T|`;
* `near_part_sum_le`: `∑_I |⟨f 1_{3 I_T}, ψ_I⟩|² ≲ (A² + B) λ² |I_T|`;
* `tile_energy_abstract`: their sum.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Two summation lemmas -/

/-- If the finite partial sums satisfy a uniform bound on `∑_i (∑_{j ∈ S} u i j)²`, so do the
`tsum`s (the sum over `i` being finite). -/
theorem sum_sq_tsum_le_of_forall_finset {ι κ : Type*} (Q : Finset ι) (u : ι → κ → ℝ) {B : ℝ}
    (hsum : ∀ i ∈ Q, Summable (u i))
    (hB : ∀ S : Finset κ, ∑ i ∈ Q, (∑ j ∈ S, u i j) ^ 2 ≤ B) :
    ∑ i ∈ Q, (∑' j, u i j) ^ 2 ≤ B := by
  have h : Tendsto (fun S : Finset κ => ∑ i ∈ Q, (∑ j ∈ S, u i j) ^ 2) atTop
      (𝓝 (∑ i ∈ Q, (∑' j, u i j) ^ 2)) := by
    refine tendsto_finsetSum Q fun i hi => ?_
    exact (show Tendsto (fun S : Finset κ => ∑ j ∈ S, u i j) atTop (𝓝 (∑' j, u i j)) from
      (hsum i hi).hasSum).pow 2
  exact le_of_tendsto' h hB

/-- **Counting by scales**: distinct dyadic intervals `I ⊆ I_T` satisfy
`∑_I |I| (|I|/|I_T|)^4 ≤ (4/3) |I_T|`. -/
theorem sum_length_mul_ratio_pow_le_gen {ι : Type*} (Q : Finset ι) (Iof : ι → Dyadic)
    (IT : Dyadic) (hinj : Set.InjOn Iof (Q : Set ι)) (hsub : ∀ i ∈ Q, (Iof i).toSet ⊆ IT.toSet) :
    ∑ i ∈ Q, (Iof i).length * ((Iof i).length / IT.length) ^ 4 ≤ 4 / 3 * IT.length := by
  classical
  have hIT := IT.length_pos
  set jf : ι → ℕ := fun i => (IT.k - (Iof i).k).toNat with hjf
  have hlen : ∀ i ∈ Q, (Iof i).length = IT.length * (1 / 2) ^ jf i := fun i hi =>
    Dyadic.length_eq_mul_half_pow (hsub i hi)
  have hclass : ∀ j : ℕ, ∑ i ∈ Q.filter (fun i => jf i = j), (Iof i).length ≤ IT.length := by
    intro j
    set F := Q.filter (fun i => jf i = j) with hF
    have hdisj : Set.PairwiseDisjoint (F : Set ι) (fun i => (Iof i).toSet) := by
      intro i hi i' hi' hne
      have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
      have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 hi')
      refine Dyadic.disjoint_of_k_eq_of_ne ?_ (fun h => hne (hinj h1.1 h2.1 h))
      have e1 : (Iof i).length = (Iof i').length := by
        rw [hlen i h1.1, hlen i' h2.1, h1.2, h2.2]
      exact Dyadic.length_eq_iff.1 e1
    have hsub' : (⋃ i ∈ F, (Iof i).toSet) ⊆ IT.toSet := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
      exact hsub i (Finset.mem_filter.1 hi).1 hxi
    have h1 := measureReal_biUnion_finset (μ := volume) hdisj
      (fun i _ => (Iof i).measurableSet_toSet) (fun i _ => by simp [Dyadic.volume_toSet])
    have h2 : volume.real (⋃ i ∈ F, (Iof i).toSet) ≤ volume.real IT.toSet :=
      measureReal_mono hsub' (by simp [Dyadic.volume_toSet])
    rw [h1] at h2
    simpa only [Dyadic.volume_real_toSet] using h2
  have hmaps : ∀ i ∈ Q, jf i ∈ Q.image jf := fun i hi => Finset.mem_image_of_mem _ hi
  calc ∑ i ∈ Q, (Iof i).length * ((Iof i).length / IT.length) ^ 4
      = ∑ j ∈ Q.image jf, ∑ i ∈ Q.filter (fun i => jf i = j),
          (Iof i).length * ((Iof i).length / IT.length) ^ 4 :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ Q.image jf, ((1 / 2 : ℝ) ^ j) ^ (2 * 2) *
          ∑ i ∈ Q.filter (fun i => jf i = j), (Iof i).length := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h1 := Finset.mem_filter.1 hi
        have : (Iof i).length / IT.length = (1 / 2 : ℝ) ^ j := by
          rw [hlen i h1.1, h1.2]; field_simp
        rw [this]; ring
    _ ≤ ∑ j ∈ Q.image jf, ((1 / 2 : ℝ) ^ j) ^ (2 * 2) * IT.length :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hclass j) (by positivity)
    _ = (∑ j ∈ Q.image jf, ((1 / 2 : ℝ) ^ j) ^ (2 * 2)) * IT.length := by rw [Finset.sum_mul]
    _ ≤ 4 / 3 * IT.length :=
        mul_le_mul_of_nonneg_right (sum_geometric_le _ (by norm_num)) hIT.le

/-! ### Packets are integrable -/

/-- The constant of an adapted packet is nonnegative. -/
theorem PacketBounds.nonneg {A : ℝ} {I : Dyadic} {ψ : ℝ → ℂ} (h : PacketBounds A I ψ) : 0 ≤ A := by
  have hL := I.length_pos
  have hs : 0 < √I.length := Real.sqrt_pos.2 hL
  have h0 := h.bound0 I.center
  have : 0 ≤ A * (√I.length)⁻¹ * (1 + |I.center - I.center| / I.length) ^ (-4 : ℤ) :=
    (norm_nonneg _).trans h0
  simp only [sub_self, abs_zero, zero_div, add_zero, one_zpow, mul_one] at this
  exact nonneg_of_mul_nonneg_left this (by positivity)

/-- An adapted packet is integrable. -/
theorem PacketBounds.integrable {A : ℝ} {I : Dyadic} {ψ : ℝ → ℂ} (h : PacketBounds A I ψ) :
    Integrable ψ := by
  have hL := I.length_pos
  have hs : 0 < √I.length := Real.sqrt_pos.2 hL
  have hA : 0 ≤ A := h.nonneg
  have hw := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) I.center hL
  refine (hw.const_mul (A * (√I.length)⁻¹)).mono' h.differentiable.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => (h.bound0 y).trans ?_)
  have h1 : (1 + |y - I.center| / I.length) ^ (-4 : ℤ) ≤
      (1 + |y - I.center| / I.length) ^ (-((2 : ℕ) : ℤ)) := by
    have : (1 : ℝ) ≤ 1 + |y - I.center| / I.length := by
      have : 0 ≤ |y - I.center| / I.length := by positivity
      linarith
    exact zpow_le_zpow_right₀ this (by norm_num)
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- A bounded measurable function times the conjugate of an integrable one is integrable. -/
theorem integrable_mul_conj_of_bounded {φ ψ : ℝ → ℂ} (hψ : Integrable ψ)
    (hφ : AEStronglyMeasurable φ volume) {M : ℝ} (hM : ∀ᵐ y, ‖φ y‖ ≤ M) :
    Integrable (fun y => φ y * conj (ψ y)) := by
  refine (hψ.norm.const_mul M).mono'
    (hφ.mul (Complex.continuous_conj.comp_aestronglyMeasurable hψ.aestronglyMeasurable)) ?_
  filter_upwards [hM] with y hy
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

/-- A point outside `3 I_T` is at distance at least `|I_T|` from the centre of `I ⊆ I_T`. -/
theorem length_le_abs_sub_center_of_notMem_dilate {I IT : Dyadic} (hI : I.toSet ⊆ IT.toSet)
    {y : ℝ} (hy : y ∉ IT.dilate 3) : IT.length ≤ |y - I.center| := by
  have hc := hI I.center_mem_toSet
  have hLT := IT.length_pos
  rw [dilate_three_eq] at hy
  have h1 := IT.right_eq
  simp only [mem_Ico, not_and_or, not_le, not_lt] at hy
  rcases hy with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [hc.1])]
    linarith [hc.1]
  · rw [abs_of_nonneg (by linarith [hc.2])]
    linarith [hc.2]

/-! ### The far part -/

section Far

variable {F : Set ℝ} {lam : ℝ} {IT : Dyadic} {f : ℝ → ℂ}

/-- **Far part, one packet** (Grafakos–Tao–Terwilleger L768-L777): for `I ⊆ I_T` with a point
outside `Ω_λ`, `|⟨f 1_{(3 I_T)ᶜ}, ψ⟩| ≤ 16 A λ √|I| (|I|/|I_T|)²`. -/
theorem norm_pairing_far_le (hF : MeasurableSet F) (hlam : 0 < lam)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) {A : ℝ} {I : Dyadic} {ψ : ℝ → ℂ}
    (hψ : PacketBounds A I ψ) (hIT : I.toSet ⊆ IT.toSet) {x' : ℝ} (hx'I : x' ∈ I.toSet)
    (hx'Ω : x' ∉ maxSuperlevel F lam) :
    ‖pairing (fun y => f y - nearPart IT f y) ψ‖ ≤
      16 * A * lam * √I.length * (I.length / IT.length) ^ 2 := by
  have hL := I.length_pos
  have hLT := IT.length_pos
  have hs : 0 < √I.length := Real.sqrt_pos.2 hL
  have hs2 : √I.length * √I.length = I.length := Real.mul_self_sqrt hL.le
  have hA := hψ.nonneg
  set w : ℝ → ℝ := fun y => (1 + |y - I.center| / I.length) ^ (-2 : ℤ) with hw
  have hwint : Integrable w := by
    have := integrable_one_add_abs_div_zpow (N := 2) (le_refl 2) I.center hL
    simpa [hw] using this
  have hwnn : ∀ y, 0 ≤ w y := fun y => by simp only [hw]; positivity
  set K := A * (√I.length)⁻¹ * (I.length / IT.length) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hg : Integrable (F.indicator (fun y => K * w y)) := (hwint.const_mul K).indicator hF
  unfold pairing
  refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · beta_reduce
    rw [norm_mul, Complex.norm_conj]
    by_cases hy3 : y ∈ IT.dilate 3
    · rw [nearPart_eq hy3, sub_self, norm_zero, zero_mul]
      exact indicator_nonneg (fun z _ => by simp only [hw]; positivity) y
    · rw [nearPart_eq_zero hy3, sub_zero]
      by_cases hyF : y ∈ F
      · rw [indicator_of_mem hyF]
        have hfy := hf y
        rw [indicator_of_mem hyF] at hfy
        have hR := length_le_abs_sub_center_of_notMem_dilate hIT hy3
        set R := IT.length / I.length with hR'
        have hRpos : 0 < R := by positivity
        have hRω : R ≤ 1 + |y - I.center| / I.length := by
          have : R ≤ |y - I.center| / I.length := by
            rw [hR']; exact div_le_div_of_nonneg_right hR hL.le
          linarith
        have h4 := zpow_neg_four_le_mul hRpos hRω
        have hψy : ‖ψ y‖ ≤ K * w y := by
          refine (hψ.bound0 y).trans ?_
          calc A * (√I.length)⁻¹ * (1 + |y - I.center| / I.length) ^ (-4 : ℤ)
              ≤ A * (√I.length)⁻¹ * (R ^ (-2 : ℤ) * (1 + |y - I.center| / I.length) ^ (-2 : ℤ)) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
            _ = K * w y := by
                simp only [hK, hw, hR']
                rw [zpow_neg, zpow_ofNat, ← inv_pow, inv_div]
                ring
        calc ‖f y‖ * ‖ψ y‖ ≤ 1 * (K * w y) := mul_le_mul hfy hψy (norm_nonneg _) zero_le_one
          _ = K * w y := one_mul _
      · have : f y = 0 := by
          have := hf y
          rw [indicator_of_notMem hyF] at this
          exact norm_le_zero_iff.1 this
        rw [this, norm_zero, zero_mul]
        exact indicator_nonneg (fun z _ => by simp only [hw]; positivity) y
  · -- the integral of the bound
    have hgood := volume_inter_Icc_two_pow_le hF hlam.le hx'I hx'Ω
    have hF16 := integral_indicator_mul_weight_le (F := F) hlam.le hL hgood
    rw [integral_indicator hF, integral_const_mul]
    calc K * ∫ y in F, w y ≤ K * (16 * lam * I.length) := mul_le_mul_of_nonneg_left hF16 hK0
      _ = 16 * A * lam * √I.length * (I.length / IT.length) ^ 2 := by
          have : (√I.length)⁻¹ * I.length = √I.length := by
            field_simp
            nlinarith [hs2]
          calc K * (16 * lam * I.length)
              = 16 * A * lam * ((√I.length)⁻¹ * I.length) * (I.length / IT.length) ^ 2 := by
                simp only [hK]; ring
            _ = _ := by rw [this]

/-- **Far part**: `∑_I |⟨f 1_{(3 I_T)ᶜ}, ψ_I⟩|² ≤ 342 A² λ² |I_T|`. -/
theorem far_part_sum_le {ι : Type*} (hF : MeasurableSet F) (hlam : 0 < lam)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) (Q : Finset ι) (Iof : ι → Dyadic)
    (ψ : ι → ℝ → ℂ) {A : ℝ} (hinj : Set.InjOn Iof (Q : Set ι))
    (hsub : ∀ i ∈ Q, (Iof i).toSet ⊆ IT.toSet)
    (hpb : ∀ i ∈ Q, PacketBounds A (Iof i) (ψ i))
    (hnot : ∀ i ∈ Q, ¬ (Iof i).toSet ⊆ maxSuperlevel F lam) :
    ∑ i ∈ Q, ‖pairing (fun y => f y - nearPart IT f y) (ψ i)‖ ^ 2 ≤
      342 * A ^ 2 * lam ^ 2 * IT.length := by
  have hLT := IT.length_pos
  have hcount := sum_length_mul_ratio_pow_le_gen Q Iof IT hinj hsub
  calc ∑ i ∈ Q, ‖pairing (fun y => f y - nearPart IT f y) (ψ i)‖ ^ 2
      ≤ ∑ i ∈ Q, 256 * A ^ 2 * lam ^ 2 * ((Iof i).length * ((Iof i).length / IT.length) ^ 4) := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨x', hx'I, hx'Ω⟩ := Set.not_subset.1 (hnot i hi)
        have h1 := norm_pairing_far_le hF hlam hf (hpb i hi) (hsub i hi) hx'I hx'Ω
        have hL := (Iof i).length_pos
        have hs2 : √(Iof i).length * √(Iof i).length = (Iof i).length :=
          Real.mul_self_sqrt hL.le
        calc ‖pairing (fun y => f y - nearPart IT f y) (ψ i)‖ ^ 2
            ≤ (16 * A * lam * √(Iof i).length * ((Iof i).length / IT.length) ^ 2) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = 256 * A ^ 2 * lam ^ 2 * ((Iof i).length * ((Iof i).length / IT.length) ^ 4) := by
              have : ((Iof i).length / IT.length) ^ 4 = (((Iof i).length / IT.length) ^ 2) ^ 2 := by
                ring
              rw [this, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hL.le]
              ring
    _ = 256 * A ^ 2 * lam ^ 2 * ∑ i ∈ Q, (Iof i).length * ((Iof i).length / IT.length) ^ 4 := by
        rw [Finset.mul_sum]
    _ ≤ 256 * A ^ 2 * lam ^ 2 * (4 / 3 * IT.length) := by gcongr
    _ ≤ 342 * A ^ 2 * lam ^ 2 * IT.length := by
        have : 0 ≤ A ^ 2 * lam ^ 2 * IT.length := by positivity
        nlinarith

end Far

/-! ### The near part -/

section Near

variable {F : Set ℝ} {lam : ℝ} {IT : Dyadic} {f : ℝ → ℂ}

open Classical in
/-- **Decomposition of the pairing of `f₀`**: `⟨f₀, ψ⟩ = ⟨g, ψ⟩ + T` where `T = ∑_J ⟨b_J, ψ⟩`
(a `HasSum` over the Calderón–Zygmund intervals). -/
theorem exists_hasSum_czTerm (hF : MeasurableSet F) (hlam : 0 < lam) {x₀ : ℝ}
    (hx₀ : x₀ ∈ IT.toSet) (hx₀Ω : x₀ ∉ maxSuperlevel F lam)
    (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) {A : ℝ} {I : Dyadic} {ψ : ℝ → ℂ}
    (hψ : PacketBounds A I ψ) :
    ∃ T : ℂ, pairing (nearPart IT f) ψ = pairing (czGood F lam IT f) ψ + T ∧
      HasSum (fun J : Dyadic => if J ∈ czFam F lam IT then czTerm IT f ψ J else 0) T := by
  classical
  set g := czGood F lam IT f with hg
  have hgm : AEStronglyMeasurable g volume := aestronglyMeasurable_czGood hfm
  have hg3 := norm_czGood_le_ae hF hlam hx₀ hx₀Ω hf
  have hn1 : Integrable (fun y => nearPart IT f y * conj (ψ y)) :=
    integrable_mul_conj_of_bounded hψ.integrable (aestronglyMeasurable_nearPart hfm) (M := 1)
      (Filter.Eventually.of_forall fun y => (norm_nearPart_le y).trans ((hf y).trans (by
        by_cases hy : y ∈ F <;> simp [hy])))
  have hn2 : Integrable (fun y => g y * conj (ψ y)) :=
    integrable_mul_conj_of_bounded hψ.integrable hgm hg3
  set h : ℝ → ℂ := fun y => (nearPart IT f y - g y) * conj (ψ y) with hh
  have hhint : Integrable h := by
    have := hn1.sub hn2
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hh, Pi.sub_apply]; ring
  refine ⟨∫ y, h y, ?_, ?_⟩
  · unfold pairing
    have : ∀ y, nearPart IT f y * conj (ψ y) = g y * conj (ψ y) + h y := fun y => by
      simp only [hh]; ring
    simp_rw [this]
    exact integral_add hn2 hhint
  · set cz : Dyadic → Set ℝ := fun J => if J ∈ czFam F lam IT then J.toSet else ∅ with hcz
    have hcz_meas : ∀ J, MeasurableSet (cz J) := by
      intro J; simp only [hcz]; split_ifs
      · exact J.measurableSet_toSet
      · exact MeasurableSet.empty
    have hcz_disj : Pairwise (Function.onFun Disjoint cz) := by
      intro J J' hne
      simp only [Function.onFun, hcz]
      split_ifs with h1 h2 h2
      · exact czFam_pairwiseDisjoint h1 h2 hne
      · exact disjoint_empty _
      · exact empty_disjoint _
      · exact disjoint_empty _
    have hU : ∫ y in ⋃ J, cz J, h y = ∫ y, h y := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
      have : ∀ J ∈ czFam F lam IT, y ∉ J.toSet := by
        intro J hJ hyJ
        exact hy (mem_iUnion.2 ⟨J, by simp only [hcz, hJ, ↓reduceIte]; exact hyJ⟩)
      simp only [hh, hg, czGood_of_forall_notMem this, sub_self, zero_mul]
    have hsum := hasSum_integral_iUnion hcz_meas hcz_disj hhint.integrableOn
    rw [hU] at hsum
    convert hsum using 1
    funext J
    by_cases hJ : J ∈ czFam F lam IT
    · simp only [hcz, hJ, ↓reduceIte, czTerm]
      refine setIntegral_congr_fun J.measurableSet_toSet fun y hy => ?_
      simp only [hh, hg, czGood_of_mem hJ hy]
    · simp only [hcz, hJ, ↓reduceIte, setIntegral_empty]

/-- The total length of disjoint dyadic intervals inside `3 I_T` is at most `3 |I_T|`. -/
theorem sum_length_le_three {S : Finset Dyadic}
    (hdisj : (S : Set Dyadic).PairwiseDisjoint Dyadic.toSet)
    (hsub : ∀ J ∈ S, J.toSet ⊆ IT.dilate 3) : ∑ J ∈ S, J.length ≤ 3 * IT.length := by
  have h1 := measureReal_biUnion_finset (μ := volume) hdisj
    (fun J _ => J.measurableSet_toSet) (fun J _ => by simp [Dyadic.volume_toSet])
  have h2 : volume.real (⋃ J ∈ S, J.toSet) ≤ volume.real (IT.dilate 3) :=
    measureReal_mono (fun x hx => by
      obtain ⟨J, hJ, hxJ⟩ := Set.mem_iUnion₂.1 hx
      exact hsub J hJ hxJ) (by rw [Dyadic.volume_dilate]; exact ENNReal.ofReal_ne_top)
  rw [h1] at h2
  simp only [Dyadic.volume_real_toSet] at h2
  have h3 : volume.real (IT.dilate 3) = 3 * IT.length := by
    simp [Measure.real, Dyadic.volume_dilate, IT.length_pos.le]
  linarith

/-- **Near part**: for `I_i ⊄ Ω_λ`,
`∑_i |⟨f 1_{3 I_T}, ψ_i⟩|² ≤ (54 B + 7260000 A²) λ² |I_T|`. -/
theorem near_part_sum_le {ι : Type*} (hF : MeasurableSet F) (hlam : 0 < lam) {x₀ : ℝ}
    (hx₀ : x₀ ∈ IT.toSet) (hx₀Ω : x₀ ∉ maxSuperlevel F lam)
    (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) (Q : Finset ι) (Iof : ι → Dyadic)
    (ψ : ι → ℝ → ℂ) {A B : ℝ} (hA0 : 0 ≤ A) (hB : 0 ≤ B) (hinj : Set.InjOn Iof (Q : Set ι))
    (hpb : ∀ i ∈ Q, PacketBounds A (Iof i) (ψ i))
    (hnot : ∀ i ∈ Q, ¬ (Iof i).toSet ⊆ maxSuperlevel F lam)
    (hbes : ∀ g : ℝ → ℂ, MemLp g 2 volume →
      ∑ i ∈ Q, ‖pairing g (ψ i)‖ ^ 2 ≤ B * ∫ x, ‖g x‖ ^ 2) :
    ∑ i ∈ Q, ‖pairing (nearPart IT f) (ψ i)‖ ^ 2 ≤
      (54 * B + 7260000 * A ^ 2) * lam ^ 2 * IT.length := by
  classical
  have hLT := IT.length_pos
  set g := czGood F lam IT f with hg
  have hgm : AEStronglyMeasurable g volume := aestronglyMeasurable_czGood hfm
  have hg3 := norm_czGood_le_ae hF hlam hx₀ hx₀Ω hf
  have hgsupp : Function.support g ⊆ IT.dilate 3 := by
    intro y hy
    by_contra hy3
    exact hy (czGood_eq_zero_of_notMem_dilate hy3)
  have hgL2 : MemLp g 2 volume :=
    memLp_two_of_bounded_of_support_subset_dilate hgm hg3 hgsupp
  -- the Bessel bound for the good function
  have hint : ∫ x, ‖g x‖ ^ 2 ≤ 27 * lam ^ 2 * IT.length := by
    have h1 : ∫ x, ‖g x‖ ^ 2 ≤
        ∫ x, (3 * lam) ^ 2 * (IT.dilate 3).indicator (fun _ => (1 : ℝ)) x := by
      refine integral_mono_ae (hgL2.norm.integrable_sq) ?_ ?_
      · exact ((integrable_indicator_iff measurableSet_Ico).2
          (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))).const_mul _
      · filter_upwards [hg3] with y hy
        by_cases hy3 : y ∈ IT.dilate 3
        · rw [indicator_of_mem hy3, mul_one]
          exact pow_le_pow_left₀ (norm_nonneg _) hy 2
        · have hgy : g y = 0 := czGood_eq_zero_of_notMem_dilate hy3
          rw [indicator_of_notMem hy3, mul_zero, hgy]
          simp
    refine h1.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) (IT.measurableSet_dilate 3),
      smul_eq_mul, mul_one, Measure.real, Dyadic.volume_dilate,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hbessel : ∑ i ∈ Q, ‖pairing g (ψ i)‖ ^ 2 ≤ B * (27 * lam ^ 2 * IT.length) :=
    (hbes g hgL2).trans (mul_le_mul_of_nonneg_left hint hB)
  choose! T hT using fun i (hi : i ∈ Q) =>
    exists_hasSum_czTerm hF hlam hx₀ hx₀Ω hfm hf (hpb i hi)
  set c : ι → ℝ := fun i => 22 * A * lam * √(Iof i).length with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by
    simp only [hc]
    have : 0 ≤ A := by
      by_cases hQ : Q.Nonempty
      · obtain ⟨i, hi⟩ := hQ; exact (hpb i hi).nonneg
      · exact hA0
    positivity
  set u : ι → Dyadic → ℝ := fun i J =>
    if J ∈ czFam F lam IT ∧ J.toSet ⊆ IT.dilate 3 then c i * kerM (Iof i) J else 0 with hu
  have hu0 : ∀ i J, 0 ≤ u i J := fun i J => by
    simp only [hu]; split_ifs
    · exact mul_nonneg (hc0 i) (kerM_nonneg _ _)
    · exact le_rfl
  -- the finite partial sums
  have hfilt : ∀ i (S : Finset Dyadic), ∑ J ∈ S, u i J = c i * ∑ J ∈ S.filter
      (fun J => J ∈ czFam F lam IT ∧ J.toSet ⊆ IT.dilate 3), kerM (Iof i) J := by
    intro i S
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp only [hu]; split_ifs <;> simp
  have hdisj' : ∀ S : Finset Dyadic, ((S.filter
      (fun J => J ∈ czFam F lam IT ∧ J.toSet ⊆ IT.dilate 3) : Finset Dyadic) :
        Set Dyadic).PairwiseDisjoint Dyadic.toSet := fun S =>
    czFam_pairwiseDisjoint.subset (fun J hJ => (Finset.mem_filter.1 hJ).2.1)
  have hrel' : ∀ i ∈ Q, ∀ S : Finset Dyadic, ∀ J ∈ S.filter
      (fun J => J ∈ czFam F lam IT ∧ J.toSet ⊆ IT.dilate 3),
      J.toSet ⊆ (Iof i).toSet ∨ Disjoint (Iof i).toSet J.toSet := fun i hi S J hJ =>
    czFam_rel (hnot i hi) (Finset.mem_filter.1 hJ).2.1
  have hrow : ∀ i ∈ Q, ∀ S : Finset Dyadic, ∑ J ∈ S, u i J ≤ c i * 25 := by
    intro i hi S
    rw [hfilt]
    refine mul_le_mul_of_nonneg_left ?_ (hc0 i)
    refine sum_kerM_le_row (Iof i) _ (hdisj' S) (fun J hJ hlt => ?_)
    rcases hrel' i hi S J hJ with h | h
    · exact absurd (Dyadic.length_le_of_subset' h) (not_le.2 hlt)
    · exact h
  have hsum : ∀ i ∈ Q, Summable (u i) := fun i hi =>
    summable_of_sum_le (c := c i * 25) (hu0 i) (hrow i hi)
  have hTle : ∀ i ∈ Q, ‖T i‖ ≤ ∑' J, u i J := by
    intro i hi
    refine ((hT i hi).2).norm_le_of_bounded (hsum i hi).hasSum (fun J => ?_)
    by_cases hJ : J ∈ czFam F lam IT
    · by_cases hJ3 : J.toSet ⊆ IT.dilate 3
      · obtain ⟨x', hx'I, hx'Ω⟩ := Set.not_subset.1 (hnot i hi)
        have := norm_czTerm_le hF hlam hx₀ hx₀Ω hfm hf (hpb i hi).nonneg (hpb i hi) hx'I hx'Ω hJ hJ3
        simp only [hJ, hJ3, hu, and_self, ↓reduceIte, hc]
        refine this.trans (le_of_eq ?_)
        ring
      · simp only [hJ, ↓reduceIte, czTerm_eq_zero hJ hJ3, norm_zero]
        exact hu0 i J
    · simp only [hJ, ↓reduceIte, norm_zero]
      exact hu0 i J
  have hschur : ∑ i ∈ Q, (∑' J, u i J) ^ 2 ≤ (22 * A * lam) ^ 2 * (7500 * IT.length) := by
    refine sum_sq_tsum_le_of_forall_finset Q u hsum fun S => ?_
    set S' := S.filter (fun J => J ∈ czFam F lam IT ∧ J.toSet ⊆ IT.dilate 3) with hS'
    have h1 := sum_length_mul_sq_kerM_le Q Iof hinj S' (hdisj' S)
      (fun i hi J hJ => hrel' i hi S J hJ)
    have h2 := sum_length_le_three (IT := IT) (hdisj' S) (fun J hJ => (Finset.mem_filter.1 hJ).2.2)
    calc ∑ i ∈ Q, (∑ J ∈ S, u i J) ^ 2
        = ∑ i ∈ Q, (22 * A * lam) ^ 2 * ((Iof i).length * (∑ J ∈ S', kerM (Iof i) J) ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hfilt, mul_pow]
          simp only [hc]
          rw [mul_pow, Real.sq_sqrt (Iof i).length_pos.le]
          ring
      _ = (22 * A * lam) ^ 2 * ∑ i ∈ Q, (Iof i).length * (∑ J ∈ S', kerM (Iof i) J) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (22 * A * lam) ^ 2 * (2500 * ∑ J ∈ S', J.length) := by gcongr
      _ ≤ (22 * A * lam) ^ 2 * (2500 * (3 * IT.length)) := by gcongr
      _ = (22 * A * lam) ^ 2 * (7500 * IT.length) := by ring
  -- combine
  calc ∑ i ∈ Q, ‖pairing (nearPart IT f) (ψ i)‖ ^ 2
      ≤ ∑ i ∈ Q, (2 * ‖pairing g (ψ i)‖ ^ 2 + 2 * (∑' J, u i J) ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [(hT i hi).1]
        have h1 := norm_add_le (pairing g (ψ i)) (T i)
        have h2 : ‖T i‖ ≤ ∑' J, u i J := hTle i hi
        have h4 : 0 ≤ ‖T i‖ := norm_nonneg _
        calc ‖pairing g (ψ i) + T i‖ ^ 2 ≤ (‖pairing g (ψ i)‖ + ‖T i‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ ≤ 2 * ‖pairing g (ψ i)‖ ^ 2 + 2 * ‖T i‖ ^ 2 := by
              nlinarith [sq_nonneg (‖pairing g (ψ i)‖ - ‖T i‖)]
          _ ≤ 2 * ‖pairing g (ψ i)‖ ^ 2 + 2 * (∑' J, u i J) ^ 2 := by
              have := pow_le_pow_left₀ h4 h2 2
              linarith
    _ = 2 * ∑ i ∈ Q, ‖pairing g (ψ i)‖ ^ 2 + 2 * ∑ i ∈ Q, (∑' J, u i J) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (B * (27 * lam ^ 2 * IT.length)) + 2 * ((22 * A * lam) ^ 2 * (7500 * IT.length)) := by
        gcongr
    _ = (54 * B + 7260000 * A ^ 2) * lam ^ 2 * IT.length := by ring

/-- **The tile-energy bound for abstract adapted packet families**
(Grafakos–Tao–Terwilleger, Lemma 1): if `ψ_i` are packets adapted to distinct dyadic intervals
`I_i ⊆ I_T`, each `I_i ⊄ Ω_λ`, obeying a Bessel inequality with constant `B`, and `|f| ≤ 1_F`, then
`∑_i |⟨f, ψ_i⟩|² ≤ 15000000 (A² + B) λ² |I_T|`. -/
theorem tile_energy_abstract {ι : Type*} (hF : MeasurableSet F) (hlam : 0 < lam)
    (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) (Q : Finset ι) (Iof : ι → Dyadic)
    (ψ : ι → ℝ → ℂ) {A B : ℝ} (hA0 : 0 ≤ A) (hB : 0 ≤ B) (hinj : Set.InjOn Iof (Q : Set ι))
    (hsub : ∀ i ∈ Q, (Iof i).toSet ⊆ IT.toSet)
    (hpb : ∀ i ∈ Q, PacketBounds A (Iof i) (ψ i))
    (hnot : ∀ i ∈ Q, ¬ (Iof i).toSet ⊆ maxSuperlevel F lam)
    (hbes : ∀ g : ℝ → ℂ, MemLp g 2 volume →
      ∑ i ∈ Q, ‖pairing g (ψ i)‖ ^ 2 ≤ B * ∫ x, ‖g x‖ ^ 2) :
    ∑ i ∈ Q, ‖pairing f (ψ i)‖ ^ 2 ≤ 15000000 * (A ^ 2 + B) * lam ^ 2 * IT.length := by
  have hLT := IT.length_pos
  have hRHS : 0 ≤ 15000000 * (A ^ 2 + B) * lam ^ 2 * IT.length := by positivity
  rcases Q.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simpa using hRHS
  obtain ⟨x₀, hx₀I, hx₀Ω⟩ := Set.not_subset.1 (hnot i₀ hi₀)
  have hx₀ : x₀ ∈ IT.toSet := hsub i₀ hi₀ hx₀I
  have hnear := near_part_sum_le hF hlam hx₀ hx₀Ω hfm hf Q Iof ψ hA0 hB hinj hpb hnot hbes
  have hfar := far_part_sum_le hF hlam hf Q Iof ψ hinj hsub hpb hnot
  have hone : ∀ y, F.indicator (fun _ => (1 : ℝ)) y ≤ 1 := fun y => by
    by_cases hy : y ∈ F <;> simp [hy]
  have hsplit : ∀ i ∈ Q, pairing f (ψ i) =
      pairing (nearPart IT f) (ψ i) + pairing (fun y => f y - nearPart IT f y) (ψ i) := by
    intro i hi
    have h1 : Integrable (fun y => nearPart IT f y * conj (ψ i y)) :=
      integrable_mul_conj_of_bounded (hpb i hi).integrable (aestronglyMeasurable_nearPart hfm)
        (M := 1) (Filter.Eventually.of_forall fun y =>
          (norm_nearPart_le y).trans ((hf y).trans (hone y)))
    have h2 : Integrable (fun y => (f y - nearPart IT f y) * conj (ψ i y)) :=
      integrable_mul_conj_of_bounded (hpb i hi).integrable
        (hfm.sub (aestronglyMeasurable_nearPart hfm)) (M := 1)
        (Filter.Eventually.of_forall fun y => by
          have h3 := norm_sub_le (f y) (nearPart IT f y)
          by_cases hy : y ∈ IT.dilate 3
          · rw [nearPart_eq hy, sub_self, norm_zero]; exact zero_le_one
          · rw [nearPart_eq_zero hy, sub_zero]; exact (hf y).trans (hone y))
    unfold pairing
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring
  calc ∑ i ∈ Q, ‖pairing f (ψ i)‖ ^ 2
      ≤ ∑ i ∈ Q, (2 * ‖pairing (nearPart IT f) (ψ i)‖ ^ 2 +
          2 * ‖pairing (fun y => f y - nearPart IT f y) (ψ i)‖ ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [hsplit i hi]
        have h1 := norm_add_le (pairing (nearPart IT f) (ψ i))
          (pairing (fun y => f y - nearPart IT f y) (ψ i))
        calc ‖pairing (nearPart IT f) (ψ i) + pairing (fun y => f y - nearPart IT f y) (ψ i)‖ ^ 2
            ≤ (‖pairing (nearPart IT f) (ψ i)‖ +
                ‖pairing (fun y => f y - nearPart IT f y) (ψ i)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ ≤ _ := by
              nlinarith [sq_nonneg (‖pairing (nearPart IT f) (ψ i)‖ -
                ‖pairing (fun y => f y - nearPart IT f y) (ψ i)‖)]
    _ = 2 * ∑ i ∈ Q, ‖pairing (nearPart IT f) (ψ i)‖ ^ 2 +
          2 * ∑ i ∈ Q, ‖pairing (fun y => f y - nearPart IT f y) (ψ i)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * ((54 * B + 7260000 * A ^ 2) * lam ^ 2 * IT.length) +
          2 * (342 * A ^ 2 * lam ^ 2 * IT.length) := by gcongr
    _ ≤ 15000000 * (A ^ 2 + B) * lam ^ 2 * IT.length := by
        have : 0 ≤ lam ^ 2 * IT.length := by positivity
        have h1 : 0 ≤ A ^ 2 := sq_nonneg A
        nlinarith [mul_nonneg h1 this, mul_nonneg hB this]

end Near

end PrimeCarleson.Proof.Oplus
