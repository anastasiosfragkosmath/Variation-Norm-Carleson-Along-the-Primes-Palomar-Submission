module

public import PrimeCarleson.Proof.Oplus.Conclusion.Covering
public import PrimeCarleson.Proof.Oplus.TilesLarge.All

/-!
# Hölder-Fubini splitting off the exceptional set ([O+] L2618-L2640)

Source: [O+] `L1except`, L2618–L2640. For finitely many functions `h_i` supported in
`E` and dyadic intervals `I_i`, and a set `G_ℓ ⊇` of the points where the covering function
`∑_i 1_{2^ℓ I_i}` is at least `B_ℓ`: the `L¹` norm of `∑_i h_i` outside `G ⊇ ⋃_ℓ G_ℓ` is at most
`∑_ℓ B_ℓ^{1/r} |E|^{1/r} (∑_i ‖h_i‖_{L^{r'}(ℝ ∖ 2^{ℓ-1} I_i)}^{r'})^{1/r'}`, the quantities `S_1`
(`ℓ = 0`) and `S_2` (`ℓ ≥ 1`) of the source. Each `x` lies in `2^ℓ I_i` for a least `ℓ`, and then
outside `2^{ℓ-1} I_i`; Hölder's inequality in the sum over `i` (exponents `r`, `r'`) and in `x` over
`E` (the factor `|E|^{1/r}`), and Tonelli for the finite sum, give the bound (L2631-L2632).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Holder

/-- **Hölder in the sum and in the variable** (L2631-L2632). -/
theorem block_holder {ι : Type*} (s : Finset ι) {r : ℝ} (hr : 1 < r) (U : ι → Set ℝ)
    (u : ι → ℝ → ℝ≥0∞) (hu : ∀ i, Measurable (u i)) {E : Set ℝ}
    (hE : MeasurableSet E) {G : Set ℝ} (hGm : MeasurableSet G) (hsupp : ∀ i x, x ∉ E → u i x = 0)
    {B : ℝ≥0∞} (hG : ∀ x, x ∉ G → ∑ i ∈ s, (U i).indicator (fun _ => (1 : ℝ≥0∞)) x ≤ B) :
    ∫⁻ x in Gᶜ, ∑ i ∈ s, (U i).indicator (u i) x ≤
      B ^ (1 / r) * volume E ^ (1 / r) *
        (∑ i ∈ s, ∫⁻ x, u i x ^ (Real.conjExponent r)) ^ (1 / Real.conjExponent r) := by
  classical
  have hH := Real.HolderConjugate.conjExponent hr
  set r' := Real.conjExponent r with hr'
  have hr0 : 0 < r := by linarith
  have hr'0 : 0 < r' := hH.symm.pos
  set w : ℝ → ℝ≥0∞ := fun x => (∑ i ∈ s, u i x ^ r') ^ (1 / r') with hw
  have hwm : Measurable w := by
    refine Measurable.pow_const (Finset.measurable_sum _ fun i _ => (hu i).pow_const _) _
  have hpt : ∀ x, x ∉ G → ∑ i ∈ s, (U i).indicator (u i) x ≤ B ^ (1 / r) * w x := by
    intro x hx
    have h1 : ∑ i ∈ s, (U i).indicator (u i) x =
        ∑ i ∈ s, (U i).indicator (fun _ => (1 : ℝ≥0∞)) x * u i x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hxi : x ∈ U i <;> simp [hxi]
    rw [h1]
    refine (ENNReal.inner_le_Lp_mul_Lq s (fun i => (U i).indicator (fun _ => (1 : ℝ≥0∞)) x)
      (fun i => u i x) hH).trans ?_
    refine mul_le_mul' ?_ le_rfl
    calc (∑ i ∈ s, ((U i).indicator (fun _ => (1 : ℝ≥0∞)) x) ^ r) ^ (1 / r)
        = (∑ i ∈ s, (U i).indicator (fun _ => (1 : ℝ≥0∞)) x) ^ (1 / r) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hxi : x ∈ U i <;> simp [hxi, hr0]
      _ ≤ B ^ (1 / r) := ENNReal.rpow_le_rpow (hG x hx) (by positivity)
  have hwE : ∀ x, x ∉ E → w x = 0 := by
    intro x hx
    simp only [hw]
    have : ∑ i ∈ s, u i x ^ r' = 0 := Finset.sum_eq_zero fun i _ => by
      rw [hsupp i x hx]; exact ENNReal.zero_rpow_of_pos hr'0
    rw [this]; exact ENNReal.zero_rpow_of_pos (by positivity)
  calc ∫⁻ x in Gᶜ, ∑ i ∈ s, (U i).indicator (u i) x
      ≤ ∫⁻ x in Gᶜ, B ^ (1 / r) * w x := by
        exact setLIntegral_mono' hGm.compl fun x hx => hpt x hx
    _ ≤ ∫⁻ x, B ^ (1 / r) * w x := setLIntegral_le_lintegral _ _
    _ = B ^ (1 / r) * ∫⁻ x, w x := lintegral_const_mul _ hwm
    _ = B ^ (1 / r) * ∫⁻ x in E, w x := by
        congr 1
        rw [← lintegral_indicator hE]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ E
        · simp [hx]
        · simp [hx, hwE x hx]
    _ ≤ B ^ (1 / r) * (volume E ^ (1 / r) * (∑ i ∈ s, ∫⁻ x, u i x ^ r') ^ (1 / r')) := by
        gcongr
        have := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict E) hH.symm
          (f := w) (g := fun _ => 1) hwm.aemeasurable aemeasurable_const
        simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
          Measure.restrict_apply_univ, one_mul] at this
        refine this.trans ?_
        rw [mul_comm]
        refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (le_of_eq ?_) (by positivity))
        have hwr : ∀ x, w x ^ r' = ∑ i ∈ s, u i x ^ r' := fun x => by
          simp only [hw]
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr'0.ne', ENNReal.rpow_one]
        simp_rw [hwr]
        rw [lintegral_finsetSum _ fun i _ => (hu i).pow_const _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← lintegral_indicator hE]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ E
        · simp [hx]
        · simp [hx, hsupp i x hx, ENNReal.zero_rpow_of_pos hr'0]
    _ = _ := by ring

/-- The region outside `2^{ℓ-1} I` (all of `ℝ` for `ℓ = 0`). -/
def tailSet (I : Dyadic) : ℕ → Set ℝ
  | 0 => univ
  | n + 1 => (I.dilate ((2 : ℝ) ^ n))ᶜ

/-- The regions `tailSet I ℓ` are measurable. -/
theorem measurableSet_tailSet (I : Dyadic) (ℓ : ℕ) : MeasurableSet (tailSet I ℓ) := by
  cases ℓ with
  | zero => exact MeasurableSet.univ
  | succ n => exact (I.measurableSet_dilate _).compl

/-- **Every point lies in one annulus** `2^ℓ I ∖ 2^{ℓ-1} I` (L2618-L2630): the value `‖h x‖` is one
of the terms of the sum over `ℓ`. -/
theorem enorm_le_tsum_annuli (I : Dyadic) (h : ℝ → ℂ) (x : ℝ) :
    ‖h x‖ₑ ≤ ∑' ℓ : ℕ, ((I.dilate ((2 : ℝ) ^ ℓ)).indicator
      (fun y => (tailSet I ℓ).indicator (fun z => ‖h z‖ₑ) y)) x := by
  classical
  have hex : ∃ ℓ : ℕ, x ∈ I.dilate ((2 : ℝ) ^ ℓ) := by
    have : x ∈ ⋃ n : ℕ, I.dilate ((2 : ℝ) ^ (n + 1)) := by rw [I.iUnion_dilate_pow]; trivial
    obtain ⟨n, hn⟩ := mem_iUnion.1 this
    exact ⟨n + 1, hn⟩
  set ℓ₀ := Nat.find hex with hℓ₀
  have hmem : x ∈ I.dilate ((2 : ℝ) ^ ℓ₀) := Nat.find_spec hex
  have htail : x ∈ tailSet I ℓ₀ := by
    cases h0 : ℓ₀ with
    | zero => exact mem_univ _
    | succ n =>
      have : ¬ x ∈ I.dilate ((2 : ℝ) ^ n) := Nat.find_min hex (by omega)
      exact this
  refine le_trans ?_ (ENNReal.le_tsum ℓ₀)
  simp [Set.indicator_of_mem hmem, Set.indicator_of_mem htail]

/-- **The `L¹` norm outside `G` of a finite sum** (L2618-L2632). If `h_i` is supported in `E`, `G`
contains the sets `G_ℓ` and off `G_ℓ` the covering function `∑_i 1_{2^ℓ I_i}` is at most `B_ℓ`, then
`∫_{ℝ ∖ G} ∑_i |h_i| ≤ ∑_ℓ B_ℓ^{1/r} |E|^{1/r}
(∑_i ‖h_i‖_{L^{r'}(ℝ ∖ 2^{ℓ-1} I_i)}^{r'})^{1/r'}`. -/
theorem stage_bound {ι : Type*} (s : Finset ι) {r : ℝ} (hr : 1 < r) (I : ι → Dyadic)
    (h : ι → ℝ → ℂ) (hm : ∀ i, Measurable (h i)) {E : Set ℝ} (hE : MeasurableSet E)
    (hsupp : ∀ i x, x ∉ E → h i x = 0) {G : Set ℝ} (Gℓ : ℕ → Set ℝ) (hGsub : ∀ ℓ, Gℓ ℓ ⊆ G)
    (hGm : ∀ ℓ, MeasurableSet (Gℓ ℓ)) (B : ℕ → ℝ≥0∞)
    (hG : ∀ ℓ x, x ∉ Gℓ ℓ →
      ∑ i ∈ s, ((I i).dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ≥0∞)) x ≤ B ℓ) :
    ∫⁻ x in Gᶜ, ∑ i ∈ s, ‖h i x‖ₑ ≤ ∑' ℓ : ℕ, B ℓ ^ (1 / r) * volume E ^ (1 / r) *
      (∑ i ∈ s, ∫⁻ x, ((tailSet (I i) ℓ).indicator (fun y => ‖h i y‖ₑ) x) ^
        Real.conjExponent r) ^ (1 / Real.conjExponent r) := by
  have hr'0 : 0 < Real.conjExponent r := (Real.HolderConjugate.conjExponent hr).symm.pos
  set u : ι → ℕ → ℝ → ℝ≥0∞ := fun i ℓ => (tailSet (I i) ℓ).indicator (fun y => ‖h i y‖ₑ)
    with hu
  have hum : ∀ i ℓ, Measurable (u i ℓ) := fun i ℓ =>
    (hm i).enorm.indicator (measurableSet_tailSet _ _)
  have hupp : ∀ i ℓ x, x ∉ E → u i ℓ x = 0 := by
    intro i ℓ x hx
    simp [hu, hsupp i x hx]
  have hterm : ∀ ℓ, Measurable fun x => ∑ i ∈ s, ((I i).dilate ((2 : ℝ) ^ ℓ)).indicator (u i ℓ) x :=
    fun ℓ => Finset.measurable_sum _ fun i _ => (hum i ℓ).indicator ((I i).measurableSet_dilate _)
  calc ∫⁻ x in Gᶜ, ∑ i ∈ s, ‖h i x‖ₑ
      ≤ ∫⁻ x in Gᶜ, ∑' ℓ : ℕ, ∑ i ∈ s, ((I i).dilate ((2 : ℝ) ^ ℓ)).indicator (u i ℓ) x := by
        refine lintegral_mono fun x => ?_
        calc ∑ i ∈ s, ‖h i x‖ₑ
            ≤ ∑ i ∈ s, ∑' ℓ : ℕ, ((I i).dilate ((2 : ℝ) ^ ℓ)).indicator (u i ℓ) x :=
              Finset.sum_le_sum fun i _ => enorm_le_tsum_annuli (I i) (h i) x
          _ = ∑' ℓ : ℕ, ∑ i ∈ s, ((I i).dilate ((2 : ℝ) ^ ℓ)).indicator (u i ℓ) x :=
              (Summable.tsum_finsetSum fun i _ => ENNReal.summable).symm
    _ = ∑' ℓ : ℕ, ∫⁻ x in Gᶜ, ∑ i ∈ s, ((I i).dilate ((2 : ℝ) ^ ℓ)).indicator (u i ℓ) x :=
        lintegral_tsum fun ℓ => (hterm ℓ).aemeasurable
    _ ≤ ∑' ℓ : ℕ, ∫⁻ x in (Gℓ ℓ)ᶜ, ∑ i ∈ s, ((I i).dilate ((2 : ℝ) ^ ℓ)).indicator (u i ℓ) x :=
        ENNReal.tsum_le_tsum fun ℓ => lintegral_mono_set (compl_subset_compl.2 (hGsub ℓ))
    _ ≤ _ := ENNReal.tsum_le_tsum fun ℓ =>
        block_holder s hr (fun i => (I i).dilate ((2 : ℝ) ^ ℓ)) (fun i => u i ℓ) (hum · ℓ) hE
          (hGm ℓ) (hupp · ℓ) (hG ℓ)

end Holder

end PrimeCarleson.Proof.Oplus
