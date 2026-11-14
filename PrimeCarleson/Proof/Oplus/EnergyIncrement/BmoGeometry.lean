module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Geometry

/-!
# Dyadic BMO norm and the geometry of dilates ([O+] L1435-L1437, L1648-L1661)

`‖·‖_BMO` is the dyadic BMO norm `‖g‖_BMO = sup_J (1/|J|) ∫_J |g - g_J|` over all dyadic
intervals `J` (L1447); here `dyadicBMO g` is this supremum in `ℝ≥0∞`.

* `Dyadic.length_le_and_subset_dilate`: a dyadic interval `J` that meets but is not contained in
  `2^ℓ I` satisfies `|I| ≤ |J|` and `I ⊆ 2^{ℓ+1} J` (the dilates of dyadic intervals have end
  points in `2^{k_I - 1} ℤ`, a lattice argument as in `Dyadic.toSet_subset_or_disjoint_of_k_le`);
* `dyadicBMO_sum_dilate_indicator_le`: if for every dyadic `J`
  `∑_{T : 2^ℓ I_T ∩ J ≠ ∅, J ⊄ 2^ℓ I_T} |I_T| ≤ A |J|` then
  `‖∑_T 1_{2^ℓ I_T}‖_BMO ≤ 2 · 2^ℓ A` (L1648-L1661: the trees with `J ⊆ 2^ℓ I_T` contribute a
  constant on `J`, those missing `J` contribute `0`, and the others have total oscillation
  at most `2 ∑ |2^ℓ I_T ∩ J|`).

Used for the consequence `‖∑_{T ∈ 𝒯} 1_{2^ℓ I_T}‖_BMO ≲ 2^{2ℓ} e^{-2}` of `bmosummeasures` of
the energy increment ([O+] L1648-L1661).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Lattice geometry of dilates -/

/-- A dyadic interval `J` meeting an interval with end points in `2^{k_J} ℤ` lies in it. -/
theorem Dyadic.toSet_subset_Ico_of_nonempty_inter (J : Dyadic) {a b : ℤ}
    (h : (Ico ((2 : ℝ) ^ J.k * a) ((2 : ℝ) ^ J.k * b) ∩ J.toSet).Nonempty) :
    J.toSet ⊆ Ico ((2 : ℝ) ^ J.k * a) ((2 : ℝ) ^ J.k * b) := by
  obtain ⟨y, ⟨hy1, hy2⟩, hy3, hy4⟩ := h
  have hp : (0 : ℝ) < (2 : ℝ) ^ J.k := zpow_pos (by norm_num) _
  have hJl : J.left = (2 : ℝ) ^ J.k * (J.m : ℝ) := rfl
  have hJr : J.right = (2 : ℝ) ^ J.k * ((J.m : ℝ) + 1) := rfl
  rw [hJl] at hy3
  rw [hJr] at hy4
  have h1 : (a : ℝ) < J.m + 1 := lt_of_mul_lt_mul_left (lt_of_le_of_lt hy1 hy4) hp.le
  have h2 : (J.m : ℝ) < b := lt_of_mul_lt_mul_left (lt_of_le_of_lt hy3 hy2) hp.le
  have h1' : a ≤ J.m := by
    have : a < J.m + 1 := by exact_mod_cast h1
    omega
  have h2' : J.m + 1 ≤ b := by
    have : J.m < b := by exact_mod_cast h2
    omega
  have h1'' : (a : ℝ) ≤ J.m := by exact_mod_cast h1'
  have h2'' : (J.m : ℝ) + 1 ≤ b := by exact_mod_cast h2'
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [hJl] at hx1
  rw [hJr] at hx2
  exact ⟨(mul_le_mul_of_nonneg_left h1'' hp.le).trans hx1,
    lt_of_lt_of_le hx2 (mul_le_mul_of_nonneg_left h2'' hp.le)⟩

/-- The dilate `2^ℓ I` of a strictly larger dyadic interval `I` has end points in `2^{k_J} ℤ`. -/
theorem Dyadic.dilate_eq_Ico_of_lt (I J : Dyadic) (ℓ : ℕ) (h : J.k < I.k) :
    ∃ a b : ℤ, I.dilate (2 ^ ℓ) = Ico ((2 : ℝ) ^ J.k * a) ((2 : ℝ) ^ J.k * b) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, I.k = J.k + 1 + n := ⟨(I.k - J.k - 1).toNat, by omega⟩
  have hk : (2 : ℝ) ^ I.k = (2 : ℝ) ^ J.k * 2 * 2 ^ n := by
    rw [hn, zpow_add₀ (by norm_num), zpow_add_one₀ (by norm_num), zpow_natCast]
  refine ⟨2 ^ n * (2 * I.m + 1 - 2 ^ ℓ), 2 ^ n * (2 * I.m + 1 + 2 ^ ℓ), ?_⟩
  unfold Dyadic.dilate Dyadic.center Dyadic.length
  rw [hk]
  push_cast
  congr 1 <;> ring

/-- A dyadic interval `J` meeting but not contained in a dilate `2^ℓ I` has `|I| ≤ |J|`. -/
theorem Dyadic.length_le_of_dilate_meets (I J : Dyadic) (ℓ : ℕ)
    (h1 : (I.dilate (2 ^ ℓ) ∩ J.toSet).Nonempty) (h2 : ¬ J.toSet ⊆ I.dilate (2 ^ ℓ)) :
    I.length ≤ J.length := by
  by_contra hlt
  obtain ⟨a, b, hab⟩ := I.dilate_eq_Ico_of_lt J ℓ (Dyadic.length_lt_iff.1 (not_le.1 hlt))
  rw [hab] at h1 h2
  exact h2 (J.toSet_subset_Ico_of_nonempty_inter h1)

/-- If a dyadic interval `J` meets but is not contained in `2^ℓ I`, then `|I| ≤ |J|` and
`I ⊆ 2^{ℓ+1} J` ([O+] L1648-L1661). -/
theorem Dyadic.length_le_and_subset_dilate (I J : Dyadic) (ℓ : ℕ)
    (h1 : (I.dilate (2 ^ ℓ) ∩ J.toSet).Nonempty) (h2 : ¬ J.toSet ⊆ I.dilate (2 ^ ℓ)) :
    I.length ≤ J.length ∧ I.toSet ⊆ J.dilate (2 ^ (ℓ + 1)) := by
  have hle := Dyadic.length_le_of_dilate_meets I J ℓ h1 h2
  refine ⟨hle, ?_⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp only [pow_zero, Dyadic.dilate_one] at h1
    obtain ⟨y, hy1, hy2⟩ := h1
    have hnd : ¬ Disjoint I.toSet J.toSet := Set.not_disjoint_iff.2 ⟨y, hy1, hy2⟩
    exact (Dyadic.toSet_subset_of_length_le_of_not_disjoint hle hnd).trans
      (J.toSet_subset_dilate (by norm_num))
  · obtain ⟨y, ⟨hyD1, hyD2⟩, hyJ1, hyJ2⟩ := h1
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hP : (2 : ℝ) ≤ 2 ^ ℓ := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
    have hP0 : (0 : ℝ) ≤ 2 ^ ℓ := by positivity
    have hJpos := J.length_pos
    have hIpos := I.length_pos
    have hPI : (2 : ℝ) ^ ℓ * I.length ≤ 2 ^ ℓ * J.length := mul_le_mul_of_nonneg_left hle hP0
    have hPJ : 2 * J.length ≤ (2 : ℝ) ^ ℓ * J.length := mul_le_mul_of_nonneg_right hP hJpos.le
    have hcI := I.center_eq
    have hcJ := J.center_eq
    have hrI := I.right_eq
    have hrJ := J.right_eq
    have e1 : ((2 : ℝ) ^ (ℓ + 1)) = 2 ^ ℓ * 2 := pow_succ _ _
    constructor
    · change J.center - (2 : ℝ) ^ (ℓ + 1) * J.length / 2 ≤ x
      rw [e1]
      change I.left ≤ x at hx1
      change J.left ≤ y at hyJ1
      change y < I.center + (2 : ℝ) ^ ℓ * I.length / 2 at hyD2
      nlinarith
    · change x < J.center + (2 : ℝ) ^ (ℓ + 1) * J.length / 2
      rw [e1]
      change x < I.right at hx2
      change y < J.right at hyJ2
      change I.center - (2 : ℝ) ^ ℓ * I.length / 2 ≤ y at hyD1
      nlinarith

/-! ### The dyadic BMO norm -/

/-- The dyadic BMO norm `sup_J (1/|J|) ∫_J |g - g_J|`, valued in `ℝ≥0∞` ([O+] L1447). -/
def dyadicBMO (g : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ J : Dyadic, ⨍⁻ y in J.toSet, ‖g y - (⨍ z in J.toSet, g z ∂volume)‖ₑ ∂volume

/-- The Lebesgue measure of the dilate `C I` is `C |I|`. -/
theorem Dyadic.volume_dilate (I : Dyadic) (C : ℝ) :
    volume (I.dilate C) = ENNReal.ofReal (C * I.length) := by
  rw [Dyadic.dilate, Real.volume_Ico]
  congr 1
  ring

/-- The dilate `C I` is measurable. -/
theorem Dyadic.measurableSet_dilate (I : Dyadic) (C : ℝ) : MeasurableSet (I.dilate C) :=
  measurableSet_Ico

/-- The oscillation of `n₀ + s` on `J`, for a nonnegative integrable function `s`, is at most
`2 ∫_J s / |J|`. -/
theorem laverage_enorm_sub_setAverage_le (J : Dyadic) {g s : ℝ → ℝ} (n₀ : ℝ)
    (hs0 : ∀ y, 0 ≤ s y) (hsi : IntegrableOn s J.toSet)
    (hg : ∀ y ∈ J.toSet, g y = n₀ + s y) :
    ⨍⁻ y in J.toSet, ‖g y - (⨍ z in J.toSet, g z ∂volume)‖ₑ ∂volume ≤
      2 * (∫⁻ y in J.toSet, ENNReal.ofReal (s y)) / volume J.toSet := by
  have hJm := J.measurableSet_toSet
  have hJv : volume J.toSet = ENNReal.ofReal J.length := J.volume_toSet
  have hJpos := J.length_pos
  have hJreal : volume.real J.toSet = J.length := by
    rw [Measure.real, hJv, ENNReal.toReal_ofReal hJpos.le]
  have hJfin : volume J.toSet ≠ ∞ := by rw [hJv]; exact ENNReal.ofReal_ne_top
  set m : ℝ := ⨍ z in J.toSet, s z ∂volume with hm
  have hm0 : 0 ≤ m := by
    rw [hm, setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 (by rw [hJreal]; exact hJpos.le))
      (setIntegral_nonneg hJm fun y _ => hs0 y)
  have hmJ : m * J.length = ∫ z in J.toSet, s z := by
    rw [hm, setAverage_eq, smul_eq_mul, hJreal]
    field_simp
  have hga : ⨍ z in J.toSet, g z ∂volume = n₀ + m := by
    rw [setAverage_eq, smul_eq_mul, hJreal]
    have : ∫ z in J.toSet, g z = ∫ z in J.toSet, (n₀ + s z) :=
      setIntegral_congr_fun hJm fun y hy => hg y hy
    rw [this, integral_add (integrableOn_const hJfin) hsi, setIntegral_const, hJreal,
      smul_eq_mul, ← hmJ]
    field_simp
  have hpt : ∀ y ∈ J.toSet, ‖g y - (⨍ z in J.toSet, g z ∂volume)‖ₑ ≤
      ENNReal.ofReal (s y) + ENNReal.ofReal m := by
    intro y hy
    rw [hga, hg y hy]
    have : n₀ + s y - (n₀ + m) = s y - m := by ring
    rw [this]
    calc ‖s y - m‖ₑ ≤ ‖s y‖ₑ + ‖m‖ₑ := enorm_sub_le
      _ = _ := by rw [Real.enorm_of_nonneg (hs0 y), Real.enorm_of_nonneg hm0]
  have hint : ∫⁻ y in J.toSet, ENNReal.ofReal (s y) = ENNReal.ofReal (∫ z in J.toSet, s z) :=
    (ofReal_integral_eq_lintegral_ofReal hsi (Filter.Eventually.of_forall hs0)).symm
  rw [laverage_eq, Measure.restrict_apply_univ]
  refine ENNReal.div_le_div_right ?_ _
  calc ∫⁻ y in J.toSet, ‖g y - (⨍ z in J.toSet, g z ∂volume)‖ₑ
      ≤ ∫⁻ y in J.toSet, (ENNReal.ofReal (s y) + ENNReal.ofReal m) :=
        setLIntegral_mono' hJm hpt
    _ = (∫⁻ y in J.toSet, ENNReal.ofReal (s y)) + ENNReal.ofReal m * volume J.toSet := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ]
    _ = 2 * (∫⁻ y in J.toSet, ENNReal.ofReal (s y)) := by
        rw [hint, hJv, ← ENNReal.ofReal_mul hm0, hmJ, two_mul]

open Classical in
/-- The oscillation on `J` of a sum of indicators of measurable sets `D t` is at most
`2 ∑ vol(D t) / |J|`, where the sum runs over the `t` whose set meets `J` without containing it
(the others contribute a constant on `J`). -/
theorem laverage_enorm_sub_setAverage_sum_indicator_le {ι : Type*} (𝒯 S : Finset ι)
    (D : ι → Set ℝ) (hD : ∀ t, MeasurableSet (D t)) (J : Dyadic)
    (hS : ∀ t, t ∈ S ↔ t ∈ 𝒯 ∧ (D t ∩ J.toSet).Nonempty ∧ ¬ J.toSet ⊆ D t) :
    ⨍⁻ y in J.toSet, ‖(∑ t ∈ 𝒯, (D t).indicator (fun _ => (1 : ℝ)) y) -
        (⨍ z in J.toSet, ∑ t ∈ 𝒯, (D t).indicator (fun _ => (1 : ℝ)) z ∂volume)‖ₑ ∂volume ≤
      2 * (∑ t ∈ S, volume (D t)) / volume J.toSet := by
  have hJfin : volume J.toSet ≠ ∞ := by rw [J.volume_toSet]; exact ENNReal.ofReal_ne_top
  have hSsub : S ⊆ 𝒯 := fun t ht => ((hS t).1 ht).1
  set s : ℝ → ℝ := fun y => ∑ t ∈ S, (D t).indicator (fun _ => (1 : ℝ)) y with hs
  have hs0 : ∀ y, 0 ≤ s y := fun y =>
    Finset.sum_nonneg fun t _ => Set.indicator_nonneg (fun _ _ => zero_le_one) y
  have hsi : IntegrableOn s J.toSet :=
    integrable_finsetSum S fun t _ => (integrableOn_const hJfin).indicator (hD t)
  have hg : ∀ y ∈ J.toSet, (∑ t ∈ 𝒯, (D t).indicator (fun _ => (1 : ℝ)) y) =
      ((𝒯.filter (fun t => J.toSet ⊆ D t)).card : ℝ) + s y := by
    intro y hy
    have h1 : ∀ t ∈ 𝒯, (D t).indicator (fun _ => (1 : ℝ)) y =
        (if J.toSet ⊆ D t then (1 : ℝ) else 0) +
          (if t ∈ S then (D t).indicator (fun _ => (1 : ℝ)) y else 0) := by
      intro t ht
      by_cases hsub : J.toSet ⊆ D t
      · have htS : t ∉ S := fun h => ((hS t).1 h).2.2 hsub
        simp [hsub, htS, hsub hy]
      · by_cases hne : (D t ∩ J.toSet).Nonempty
        · have htS : t ∈ S := (hS t).2 ⟨ht, hne, hsub⟩
          simp [hsub, htS]
        · have htS : t ∉ S := fun h => hne ((hS t).1 h).2.1
          have hy' : y ∉ D t := fun h => hne ⟨y, h, hy⟩
          simp [hsub, htS, hy']
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_boole,
      Finset.sum_ite_mem, Finset.inter_eq_right.2 hSsub]
  refine (laverage_enorm_sub_setAverage_le J _ hs0 hsi hg).trans ?_
  refine ENNReal.div_le_div_right (mul_le_mul' le_rfl ?_) _
  have hmeas : ∀ t ∈ S, Measurable ((D t).indicator (fun _ => (1 : ℝ≥0∞))) := fun t _ =>
    measurable_const.indicator (hD t)
  calc ∫⁻ y in J.toSet, ENNReal.ofReal (s y)
      = ∫⁻ y in J.toSet, ∑ t ∈ S, (D t).indicator (fun _ => (1 : ℝ≥0∞)) y := by
        refine lintegral_congr fun y => ?_
        rw [hs, ENNReal.ofReal_sum_of_nonneg fun t _ =>
          Set.indicator_nonneg (fun _ _ => zero_le_one) y]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hy : y ∈ D t <;> simp [hy]
    _ = ∑ t ∈ S, ∫⁻ y in J.toSet, (D t).indicator (fun _ => (1 : ℝ≥0∞)) y :=
        lintegral_finsetSum S hmeas
    _ = ∑ t ∈ S, (volume.restrict J.toSet) (D t) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [lintegral_indicator_const (hD t), one_mul]
    _ ≤ ∑ t ∈ S, volume (D t) :=
        Finset.sum_le_sum fun t _ => Measure.restrict_apply_le _ _

open Classical in
/-- The dyadic BMO norm of `∑_{T ∈ 𝒯} 1_{2^ℓ I_T}` is at most `2 · 2^ℓ A` when
`∑_{T : 2^ℓ I_T ∩ J ≠ ∅, J ⊄ 2^ℓ I_T} |I_T| ≤ A |J|` for every dyadic `J` ([O+] L1648-L1661). -/
theorem dyadicBMO_sum_dilate_indicator_le {ι : Type*} (𝒯 : Finset ι) (I : ι → Dyadic) (ℓ : ℕ)
    {A : ℝ} (hA : ∀ J : Dyadic, ∑ t ∈ 𝒯.filter (fun t => ((I t).dilate (2 ^ ℓ) ∩ J.toSet).Nonempty ∧
        ¬ J.toSet ⊆ (I t).dilate (2 ^ ℓ)), (I t).length ≤ A * J.length) :
    dyadicBMO (fun x => ∑ t ∈ 𝒯, ((I t).dilate (2 ^ ℓ)).indicator (fun _ => (1 : ℝ)) x) ≤
      ENNReal.ofReal (2 * 2 ^ ℓ * A) := by
  unfold dyadicBMO
  refine iSup_le fun J => ?_
  have hJpos := J.length_pos
  have hbd := laverage_enorm_sub_setAverage_sum_indicator_le 𝒯
    (𝒯.filter (fun t => ((I t).dilate (2 ^ ℓ) ∩ J.toSet).Nonempty ∧
      ¬ J.toSet ⊆ (I t).dilate (2 ^ ℓ))) (fun t => (I t).dilate (2 ^ ℓ))
    (fun t => (I t).measurableSet_dilate _) J (fun t => by simp [Finset.mem_filter])
  refine hbd.trans ?_
  have hsum : ∑ t ∈ 𝒯.filter (fun t => ((I t).dilate (2 ^ ℓ) ∩ J.toSet).Nonempty ∧
      ¬ J.toSet ⊆ (I t).dilate (2 ^ ℓ)), volume ((I t).dilate (2 ^ ℓ)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ ℓ * (A * J.length)) := by
    simp only [Dyadic.volume_dilate]
    rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => mul_nonneg (by positivity) (I t).length_pos.le,
      ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hA J) (by positivity))
  calc 2 * (∑ t ∈ 𝒯.filter (fun t => ((I t).dilate (2 ^ ℓ) ∩ J.toSet).Nonempty ∧
        ¬ J.toSet ⊆ (I t).dilate (2 ^ ℓ)), volume ((I t).dilate (2 ^ ℓ))) / volume J.toSet
      ≤ 2 * ENNReal.ofReal ((2 : ℝ) ^ ℓ * (A * J.length)) / ENNReal.ofReal J.length := by
        rw [J.volume_toSet]
        exact ENNReal.div_le_div_right (mul_le_mul' le_rfl hsum) _
    _ = ENNReal.ofReal (2 * 2 ^ ℓ * A) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_div_of_pos hJpos]
        congr 1
        field_simp

end PrimeCarleson.Proof.Oplus
