module

public import PrimeCarleson.Proof.Oplus.External.Stopping
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoGeometry

/-!
# Level sets of the dyadic maximal function: geometric decay (John–Nirenberg in stopping form)

Steps 1-3 of the proof of the interpolation between `L¹` and dyadic BMO (used for the `L^q`
bound for the covering function of [O+] L2603-L2609). For `g ≥ 0` integrable and `λ > 0` let
`Ω_λ = ⋃ {I dyadic : g_I > λ}` (the set `{M_D g > λ}`), and `b ≥ 0` a bound for the dyadic mean
oscillation, `∫_I |g - g_I| ≤ b |I|` for every dyadic `I`.

* `mul_volume_levelUnion_le` (Step 1): `λ |Ω_λ| ≤ ∫ g`;
* `dyadicMean_le_of_isMax` (Step 2): `g_I ≤ λ + 2b` for a maximal interval `I` of `{g_I > λ}`;
* `two_mul_volume_inter_le` (Step 3): `2 |Ω_{λ+4b} ∩ I| ≤ |I|` for maximal `I`;
* `two_mul_volume_levelUnion_add_le`: `2 |Ω_{λ+4b}| ≤ |Ω_λ|`, and by induction
  `2^n |Ω_{λ+4bn}| ≤ |Ω_λ|` (`two_pow_mul_volume_levelUnion_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The average `g_I = |I|⁻¹ ∫_I g` of `g` over the dyadic interval `I`. -/
def dyadicMean (g : ℝ → ℝ) (I : Dyadic) : ℝ := ⨍ y in I.toSet, g y ∂volume

/-- `g_I |I| = ∫_I g`. -/
theorem dyadicMean_mul_length (g : ℝ → ℝ) (I : Dyadic) :
    dyadicMean g I * I.length = ∫ y in I.toSet, g y := by
  have := I.length_pos
  rw [dyadicMean, setAverage_eq, smul_eq_mul, Dyadic.volume_real_toSet]
  field_simp

section Level

variable {g : ℝ → ℝ}

/-- The union `Ω_λ` of the dyadic intervals with `g_I > λ`. -/
def levelUnion (g : ℝ → ℝ) (lam : ℝ) : Set ℝ :=
  ⋃ (I : Dyadic) (_ : lam < dyadicMean g I), I.toSet

/-- The maximal dyadic intervals `I` with `g_I > λ`. -/
abbrev levelMax (g : ℝ → ℝ) (lam : ℝ) : Set Dyadic :=
  {I | Dyadic.IsMaxFor (fun J => lam < dyadicMean g J) I}

/-- `x ∈ Ω_λ` iff some dyadic interval containing `x` has `g_I > λ`. -/
theorem mem_levelUnion {lam x : ℝ} :
    x ∈ levelUnion g lam ↔ ∃ I : Dyadic, x ∈ I.toSet ∧ lam < dyadicMean g I := by
  simp only [levelUnion, mem_iUnion, exists_prop]
  exact ⟨fun ⟨I, h, hx⟩ => ⟨I, hx, h⟩, fun ⟨I, hx, h⟩ => ⟨I, h, hx⟩⟩

/-- `Ω_λ` is measurable. -/
theorem measurableSet_levelUnion (lam : ℝ) : MeasurableSet (levelUnion g lam) :=
  MeasurableSet.iUnion fun I => MeasurableSet.iUnion fun _ => I.measurableSet_toSet

/-- `Ω_λ` decreases in `λ`. -/
theorem levelUnion_anti {lam lam' : ℝ} (h : lam ≤ lam') : levelUnion g lam' ⊆ levelUnion g lam :=
  fun x hx => by
    obtain ⟨I, hxI, hI⟩ := mem_levelUnion.1 hx
    exact mem_levelUnion.2 ⟨I, hxI, lt_of_le_of_lt h hI⟩

/-- `g_I > λ` gives `λ |I| < ∫_I g`. -/
theorem mul_length_lt_setIntegral {lam : ℝ} {I : Dyadic} (h : lam < dyadicMean g I) :
    lam * I.length < ∫ y in I.toSet, g y := by
  have hI := I.length_pos
  have h1 : lam * I.length < dyadicMean g I * I.length := mul_lt_mul_of_pos_right h hI
  rwa [dyadicMean_mul_length] at h1

/-- A dyadic interval with `g_I > λ` has length `< (∫ g)/λ`. -/
theorem mul_length_lt_integral (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {lam : ℝ} {I : Dyadic}
    (h : lam < dyadicMean g I) : lam * I.length < ∫ y, g y :=
  (mul_length_lt_setIntegral h).trans_le
    (setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0))

/-- The scales of the intervals with `g_I > λ` are bounded above. -/
theorem exists_scale_bound (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {lam : ℝ} (hlam : 0 < lam) :
    ∃ K : ℤ, ∀ I : Dyadic, lam < dyadicMean g I → I.k ≤ K := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((∫ y, g y) / lam) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun I hI => ?_⟩
  have h1 := mul_length_lt_integral hg0 hgi hI
  have h2 : I.length < (2 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast]
    have : I.length < (∫ y, g y) / lam := by rw [lt_div_iff₀ hlam]; linarith
    exact this.trans hn
  have : I.k < n := by
    unfold Dyadic.length at h2
    exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2
  omega

/-- Every interval with `g_I > λ` lies in a maximal one. -/
theorem exists_levelMax_superset (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {lam : ℝ}
    (hlam : 0 < lam) {J : Dyadic} (hJ : lam < dyadicMean g J) :
    ∃ I ∈ levelMax g lam, J.toSet ⊆ I.toSet := by
  obtain ⟨K, hK⟩ := exists_scale_bound hg0 hgi hlam
  obtain ⟨I, hI, hsub⟩ := Dyadic.exists_isMaxFor_superset (fun J => lam < dyadicMean g J) K hK hJ
  exact ⟨I, hI, hsub⟩

/-- `Ω_λ` is the union of the maximal intervals. -/
theorem levelUnion_eq_biUnion (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {lam : ℝ}
    (hlam : 0 < lam) : levelUnion g lam = ⋃ I ∈ levelMax g lam, I.toSet := by
  ext x
  constructor
  · intro hx
    obtain ⟨J, hxJ, hJ⟩ := mem_levelUnion.1 hx
    obtain ⟨I, hI, hsub⟩ := exists_levelMax_superset hg0 hgi hlam hJ
    exact mem_iUnion₂.2 ⟨I, hI, hsub hxJ⟩
  · intro hx
    obtain ⟨I, hI, hxI⟩ := mem_iUnion₂.1 hx
    exact mem_levelUnion.2 ⟨I, hxI, hI.1⟩

/-- **Step 1 (weak type)**: `λ |Ω_λ| ≤ ∫ g`. -/
theorem mul_volume_levelUnion_le (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {lam : ℝ}
    (hlam : 0 < lam) :
    ENNReal.ofReal lam * volume (levelUnion g lam) ≤ ENNReal.ofReal (∫ y, g y) := by
  rw [levelUnion_eq_biUnion hg0 hgi hlam,
    measure_biUnion (Set.to_countable _) (Dyadic.pairwiseDisjoint_isMaxFor _)
      (fun I _ => I.measurableSet_toSet), ← ENNReal.tsum_mul_left]
  have hterm : ∀ I : levelMax g lam, ENNReal.ofReal lam * volume (I : Dyadic).toSet ≤
      ∫⁻ y in (I : Dyadic).toSet, ENNReal.ofReal (g y) := by
    intro I
    have h1 := mul_length_lt_setIntegral I.2.1
    rw [Dyadic.volume_toSet, ← ENNReal.ofReal_mul hlam.le,
      ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn (Filter.Eventually.of_forall hg0)]
    exact ENNReal.ofReal_le_ofReal h1.le
  calc ∑' I : levelMax g lam, ENNReal.ofReal lam * volume (I : Dyadic).toSet
      ≤ ∑' I : levelMax g lam, ∫⁻ y in (I : Dyadic).toSet, ENNReal.ofReal (g y) :=
        ENNReal.tsum_le_tsum hterm
    _ = ∫⁻ y in ⋃ I ∈ levelMax g lam, I.toSet, ENNReal.ofReal (g y) :=
        (lintegral_biUnion (Set.to_countable _) (fun I _ => I.measurableSet_toSet)
          (Dyadic.pairwiseDisjoint_isMaxFor _) _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (g y) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ y, g y) :=
        (ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)).symm

/-! ### The mean oscillation and Step 2 -/

/-- `b` bounds the mean oscillation of `g` over every dyadic interval: `∫_I |g - g_I| ≤ b |I|`. -/
def MeanOscLe (g : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ I : Dyadic, ∫ y in I.toSet, |g y - dyadicMean g I| ≤ b * I.length

/-- `|I|⁻¹ ∫_I |g - c|` is controlled on a subset: `∫_I (g - c) = (g_I - c) |I|`. -/
theorem setIntegral_sub_const_eq (hgi : Integrable g) (I : Dyadic) (c : ℝ) :
    ∫ y in I.toSet, (g y - c) = (dyadicMean g I - c) * I.length := by
  have hfin : volume I.toSet ≠ ∞ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  rw [integral_sub hgi.integrableOn (integrableOn_const hfin), setIntegral_const,
    Dyadic.volume_real_toSet, smul_eq_mul, ← dyadicMean_mul_length]
  ring

/-- **Step 2 (parent)**: `g_I - g_{Î} ≤ 2b` for the dyadic parent `Î` of `I`. -/
theorem dyadicMean_sub_parent_le (hgi : Integrable g) {b : ℝ} (hb : MeanOscLe g b) (I : Dyadic) :
    dyadicMean g I - dyadicMean g I.parent ≤ 2 * b := by
  set c := dyadicMean g I.parent with hc
  have hI := I.length_pos
  have hfin : ∀ s : Set ℝ, volume s ≠ ∞ → IntegrableOn (fun y => |g y - c|) s := fun s hs =>
    (hgi.integrableOn.sub (integrableOn_const hs)).abs
  have hfinI : volume I.toSet ≠ ∞ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  have hfinP : volume I.parent.toSet ≠ ∞ := by
    rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  have h1 := setIntegral_sub_const_eq hgi I c
  have h2 : ∫ y in I.toSet, (g y - c) ≤ ∫ y in I.toSet, |g y - c| :=
    integral_mono (hgi.integrableOn.sub (integrableOn_const hfinI)) (hfin _ hfinI)
      fun y => le_abs_self _
  have h3 : ∫ y in I.toSet, |g y - c| ≤ ∫ y in I.parent.toSet, |g y - c| :=
    setIntegral_mono_set (hfin _ hfinP) (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (Filter.Eventually.of_forall I.toSet_subset_parent)
  have h4 := hb I.parent
  rw [Dyadic.length_parent] at h4
  have h5 : (dyadicMean g I - c) * I.length ≤ 2 * b * I.length := by nlinarith
  exact le_of_mul_le_mul_right h5 hI

/-- The parent of a maximal interval does not satisfy `g_Î > λ`. -/
theorem dyadicMean_parent_le_of_isMax {lam : ℝ} {I : Dyadic} (hI : I ∈ levelMax g lam) :
    dyadicMean g I.parent ≤ lam := by
  by_contra h
  rw [not_le] at h
  have := hI.2 I.parent h I.toSet_subset_parent
  have hk := congrArg Dyadic.k this
  simp only [Dyadic.parent_k] at hk
  omega

/-- A maximal interval has `g_I ≤ λ + 2b` (Step 2). -/
theorem dyadicMean_le_of_isMax (hgi : Integrable g) {b : ℝ} (hb : MeanOscLe g b) {lam : ℝ}
    {I : Dyadic} (hI : I ∈ levelMax g lam) : dyadicMean g I ≤ lam + 2 * b := by
  have h1 := dyadicMean_sub_parent_le hgi hb I
  have h2 := dyadicMean_parent_le_of_isMax hI
  linarith

/-! ### Step 3: geometric decay -/

/-- **Step 3, one maximal interval**: `2 |Ω_{λ+4b} ∩ I| ≤ |I|` for `I` maximal with `g_I > λ`. -/
theorem two_mul_volume_inter_le (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {b : ℝ}
    (hb : MeanOscLe g b) (hb0 : 0 < b) {lam : ℝ} (hlam : 0 < lam) {I : Dyadic}
    (hI : I ∈ levelMax g lam) :
    2 * volume (levelUnion g (lam + 4 * b) ∩ I.toSet) ≤ volume I.toSet := by
  set lam' := lam + 4 * b with hlam'def
  have hlam' : 0 < lam' := by rw [hlam'def]; linarith
  set c := dyadicMean g I with hcdef
  have hc : c ≤ lam + 2 * b := dyadicMean_le_of_isMax hgi hb hI
  set S : Set Dyadic := {J | J ∈ levelMax g lam' ∧ J.toSet ⊆ I.toSet} with hS
  have hSsub : S ⊆ levelMax g lam' := fun J hJ => hJ.1
  have hU : levelUnion g lam' ∩ I.toSet = ⋃ J ∈ S, J.toSet := by
    ext x
    constructor
    · rintro ⟨hx, hxI⟩
      rw [levelUnion_eq_biUnion hg0 hgi hlam'] at hx
      obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.1 hx
      refine mem_iUnion₂.2 ⟨J, ⟨hJ, ?_⟩, hxJ⟩
      have hJlam : lam < dyadicMean g J := by have := hJ.1; linarith
      obtain ⟨I', hI', hJI'⟩ := exists_levelMax_superset hg0 hgi hlam hJlam
      by_cases hII' : I = I'
      · subst hII'; exact hJI'
      · exact absurd (hJI' hxJ) (Set.disjoint_left.1
          (Dyadic.IsMaxFor.disjoint (p := fun J => lam < dyadicMean g J) hI hI' hII') hxI)
    · intro hx
      obtain ⟨J, ⟨hJ, hJI⟩, hxJ⟩ := mem_iUnion₂.1 hx
      exact ⟨mem_levelUnion.2 ⟨J, hxJ, hJ.1⟩, hJI hxJ⟩
  have hfinI : volume I.toSet ≠ ∞ := by rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
  have hfin : ∀ s : Set ℝ, volume s ≠ ∞ → IntegrableOn (fun y => |g y - c|) s := fun s hs =>
    (hgi.integrableOn.sub (integrableOn_const hs)).abs
  have hterm : ∀ J : S, ENNReal.ofReal (2 * b) * volume (J : Dyadic).toSet ≤
      ∫⁻ y in (J : Dyadic).toSet, ENNReal.ofReal |g y - c| := by
    intro J
    have hJfin : volume (J : Dyadic).toSet ≠ ∞ := by
      rw [Dyadic.volume_toSet]; exact ENNReal.ofReal_ne_top
    have hJ1 : lam' < dyadicMean g J := J.2.1.1
    have e1 := setIntegral_sub_const_eq hgi J c
    have e2 : ∫ y in (J : Dyadic).toSet, (g y - c) ≤ ∫ y in (J : Dyadic).toSet, |g y - c| :=
      integral_mono (hgi.integrableOn.sub (integrableOn_const hJfin)) (hfin _ hJfin)
        fun y => le_abs_self _
    have e3 : 2 * b * (J : Dyadic).length ≤ (dyadicMean g J - c) * (J : Dyadic).length :=
      mul_le_mul_of_nonneg_right (by linarith) (J : Dyadic).length_pos.le
    rw [Dyadic.volume_toSet, ← ENNReal.ofReal_mul (by linarith),
      ← ofReal_integral_eq_lintegral_ofReal (hfin _ hJfin)
        (Filter.Eventually.of_forall fun y => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hdisjS : S.PairwiseDisjoint Dyadic.toSet :=
    (Dyadic.pairwiseDisjoint_isMaxFor _).subset hSsub
  have key : ENNReal.ofReal (2 * b) * volume (levelUnion g lam' ∩ I.toSet) ≤
      ENNReal.ofReal b * volume I.toSet := by
    rw [hU, measure_biUnion (Set.to_countable _) hdisjS (fun J _ => J.measurableSet_toSet),
      ← ENNReal.tsum_mul_left]
    calc ∑' J : S, ENNReal.ofReal (2 * b) * volume (J : Dyadic).toSet
        ≤ ∑' J : S, ∫⁻ y in (J : Dyadic).toSet, ENNReal.ofReal |g y - c| :=
          ENNReal.tsum_le_tsum hterm
      _ = ∫⁻ y in ⋃ J ∈ S, J.toSet, ENNReal.ofReal |g y - c| :=
          (lintegral_biUnion (Set.to_countable _) (fun J _ => J.measurableSet_toSet) hdisjS _).symm
      _ ≤ ∫⁻ y in I.toSet, ENNReal.ofReal |g y - c| := by
          refine lintegral_mono_set ?_
          intro x hx
          obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.1 hx
          exact hJ.2 hxJ
      _ = ENNReal.ofReal (∫ y in I.toSet, |g y - c|) :=
          (ofReal_integral_eq_lintegral_ofReal (hfin _ hfinI)
            (Filter.Eventually.of_forall fun y => abs_nonneg _)).symm
      _ ≤ ENNReal.ofReal (b * I.length) := ENNReal.ofReal_le_ofReal (hb I)
      _ = ENNReal.ofReal b * volume I.toSet := by
          rw [Dyadic.volume_toSet, ENNReal.ofReal_mul hb0.le]
  have hb' : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.2 hb0).ne'
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc,
    mul_left_comm] at key
  exact (ENNReal.mul_le_mul_iff_right hb' ENNReal.ofReal_ne_top).1 key

/-- **Step 3**: `2 |Ω_{λ+4b}| ≤ |Ω_λ|`. -/
theorem two_mul_volume_levelUnion_add_le (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {b : ℝ}
    (hb : MeanOscLe g b) (hb0 : 0 < b) {lam : ℝ} (hlam : 0 < lam) :
    2 * volume (levelUnion g (lam + 4 * b)) ≤ volume (levelUnion g lam) := by
  have hsub : levelUnion g (lam + 4 * b) ⊆ levelUnion g lam :=
    levelUnion_anti (by linarith)
  have hcov : levelUnion g (lam + 4 * b) =
      ⋃ I ∈ levelMax g lam, (levelUnion g (lam + 4 * b) ∩ I.toSet) := by
    ext x
    constructor
    · intro hx
      have hx' := hsub hx
      rw [levelUnion_eq_biUnion hg0 hgi hlam] at hx'
      obtain ⟨I, hI, hxI⟩ := mem_iUnion₂.1 hx'
      exact mem_iUnion₂.2 ⟨I, hI, hx, hxI⟩
    · intro hx
      obtain ⟨I, _, hxI⟩ := mem_iUnion₂.1 hx
      exact hxI.1
  have hdisj : (levelMax g lam).PairwiseDisjoint
      (fun I : Dyadic => levelUnion g (lam + 4 * b) ∩ I.toSet) :=
    (Dyadic.pairwiseDisjoint_isMaxFor _).mono fun I => inter_subset_right
  rw [hcov, measure_biUnion (Set.to_countable _) hdisj
    (fun I _ => (measurableSet_levelUnion _).inter I.measurableSet_toSet), ← ENNReal.tsum_mul_left,
    levelUnion_eq_biUnion hg0 hgi hlam,
    measure_biUnion (Set.to_countable _) (Dyadic.pairwiseDisjoint_isMaxFor _)
      (fun I _ => I.measurableSet_toSet)]
  exact ENNReal.tsum_le_tsum fun I => two_mul_volume_inter_le hg0 hgi hb hb0 hlam I.2

/-- **Geometric decay**: `2^n |Ω_{λ+4bn}| ≤ |Ω_λ|`. -/
theorem two_pow_mul_volume_levelUnion_le (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {b : ℝ}
    (hb : MeanOscLe g b) (hb0 : 0 < b) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    2 ^ n * volume (levelUnion g (lam + 4 * b * n)) ≤ volume (levelUnion g lam) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : 0 < lam + 4 * b * n := by
      have : 0 ≤ 4 * b * (n : ℝ) := by positivity
      linarith
    have h := two_mul_volume_levelUnion_add_le hg0 hgi hb hb0 hpos
    have e : lam + 4 * b * ((n + 1 : ℕ) : ℝ) = lam + 4 * b * n + 4 * b := by push_cast; ring
    rw [e]
    calc 2 ^ (n + 1) * volume (levelUnion g (lam + 4 * b * n + 4 * b))
        = 2 ^ n * (2 * volume (levelUnion g (lam + 4 * b * n + 4 * b))) := by ring
      _ ≤ 2 ^ n * volume (levelUnion g (lam + 4 * b * n)) := by gcongr
      _ ≤ _ := ih

end Level

end PrimeCarleson.Proof.Oplus
