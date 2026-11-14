module

public import PrimeCarleson.Proof.Oplus.External.Stopping
public import PrimeCarleson.Proof.Oplus.External.THMaximal
public import PrimeCarleson.Proof.Oplus.TreeSmall.Intervals

/-!
# The Calderón–Zygmund intervals of the tile-energy bound

Source: Grafakos–Tao–Terwilleger, L805–L808 and L789–L1231. For
`Ω = Ω_λ = {M[1_F] > λ}` and a
dyadic interval `I_T`, `czFam F λ I_T` is the family of dyadic intervals `J ⊂ Ω` with
`|J| ≤ |I_T|`, maximal for these properties (the intervals `J_k` of Grafakos–Tao–Terwilleger;
the cap `|J| ≤ |I_T|`
replaces the splitting of large intervals into pieces of length `|I_T|`).

* `czFam_pairwiseDisjoint`, `exists_czFam_mem_of_mem`: the elements are pairwise disjoint and cover
  `Ω` (`Ω` is open);
* `czFam_rel`: `J ∈ czFam` is inside or disjoint from every dyadic `I ⊄ Ω`;
* `subset_dilate_three_of_meets`: a dyadic `J` with `|J| ≤ |I_T|` meeting `3 I_T` lies in it;
* `volume_inter_czFam_le`: if `x₀ ∈ I_T` with `x₀ ∉ Ω` then `|F ∩ J| ≤ 3λ|J|` for every
  `J ∈ czFam` inside `3 I_T`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The property defining the Calderón–Zygmund intervals: `J ⊂ Ω_λ` and `|J| ≤ |I_T|`. -/
def czProp (F : Set ℝ) (lam : ℝ) (IT : Dyadic) (J : Dyadic) : Prop :=
  J.toSet ⊆ maxSuperlevel F lam ∧ J.k ≤ IT.k

/-- The maximal dyadic intervals `J ⊂ Ω_λ` with `|J| ≤ |I_T|`. -/
abbrev czFam (F : Set ℝ) (lam : ℝ) (IT : Dyadic) : Set Dyadic :=
  {J | Dyadic.IsMaxFor (czProp F lam IT) J}

variable {F : Set ℝ} {lam : ℝ} {IT : Dyadic}

/-- Elements of `czFam` lie in `Ω_λ`. -/
theorem czFam_subset {J : Dyadic} (hJ : J ∈ czFam F lam IT) : J.toSet ⊆ maxSuperlevel F lam :=
  hJ.1.1

/-- Elements of `czFam` have scale at most that of `I_T`. -/
theorem czFam_k_le {J : Dyadic} (hJ : J ∈ czFam F lam IT) : J.k ≤ IT.k := hJ.1.2

/-- The elements of `czFam` are pairwise disjoint. -/
theorem czFam_pairwiseDisjoint : (czFam F lam IT).PairwiseDisjoint Dyadic.toSet :=
  Dyadic.pairwiseDisjoint_isMaxFor _

/-- Every point of the open set `Ω_λ` lies in an element of `czFam`. -/
theorem exists_czFam_mem_of_mem {x : ℝ} (hx : x ∈ maxSuperlevel F lam) :
    ∃ J ∈ czFam F lam IT, x ∈ J.toSet := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_maxSuperlevel F lam) x hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  set k : ℤ := min IT.k (-(n : ℤ)) with hk
  set I := Dyadic.ofPoint k x with hI
  have hxI : x ∈ I.toSet := Dyadic.mem_toSet_ofPoint k x
  have hlen : I.length < ε := by
    have h1 : I.length = (2 : ℝ) ^ k := rfl
    have h2 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (-(n : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (min_le_right _ _)
    have h3 : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2 : ℝ) ^ n := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [h1]; rw [h3] at h2; linarith
  have hIsub : I.toSet ⊆ maxSuperlevel F lam := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have := I.right_eq
    obtain ⟨h1, h2⟩ := hxI
    obtain ⟨h3, h4⟩ := hy
    rw [abs_lt]
    constructor <;> linarith
  have hp : czProp F lam IT I := ⟨hIsub, min_le_left _ _⟩
  obtain ⟨J, hJ, hIJ⟩ := Dyadic.exists_isMaxFor_superset (czProp F lam IT) IT.k
    (fun J hJ => hJ.2) hp
  exact ⟨J, hJ, hIJ hxI⟩

/-- A maximal interval is inside or disjoint from every dyadic `I ⊄ Ω_λ`. -/
theorem czFam_rel {I J : Dyadic} (hI : ¬ I.toSet ⊆ maxSuperlevel F lam)
    (hJ : J ∈ czFam F lam IT) : J.toSet ⊆ I.toSet ∨ Disjoint I.toSet J.toSet := by
  rcases I.nested_or_disjoint J with h | h | h
  · exact absurd (h.trans (czFam_subset hJ)) hI
  · exact Or.inl h
  · exact Or.inr h

/-! ### Dyadic intervals and `3 I_T` -/

/-- `3 I_T = [left - |I_T|, right + |I_T|)`. -/
theorem dilate_three_eq (IT : Dyadic) :
    IT.dilate 3 = Ico (IT.left - IT.length) (IT.right + IT.length) := by
  unfold Dyadic.dilate
  rw [IT.center_eq, IT.right_eq]
  congr 1 <;> ring

/-- A dyadic interval `J` with `|J| ≤ |I_T|` meeting `3 I_T` lies inside `3 I_T`. -/
theorem subset_dilate_three_of_meets {J : Dyadic} (hk : J.k ≤ IT.k)
    (h : (J.toSet ∩ IT.dilate 3).Nonempty) : J.toSet ⊆ IT.dilate 3 := by
  obtain ⟨y, hyJ, hy3⟩ := h
  rw [dilate_three_eq] at hy3 ⊢
  have hL := IT.length_pos
  have hr := IT.right_eq
  -- the three cells of scale `k_T` that make up `3 I_T`
  have key : ∀ K : Dyadic, K.k = IT.k → y ∈ K.toSet →
      K.toSet ⊆ Ico (IT.left - IT.length) (IT.right + IT.length) → J.toSet ⊆
        Ico (IT.left - IT.length) (IT.right + IT.length) := by
    intro K hKk hyK hKsub
    rcases J.toSet_subset_or_disjoint_of_k_le K (hKk ▸ hk) with h | h
    · exact h.trans hKsub
    · exact absurd hyK (fun hm => Set.disjoint_left.1 h hyJ hm)
  have hlen : IT.length = (2 : ℝ) ^ IT.k := rfl
  by_cases h1 : y < IT.left
  · refine key (IT.shift (-1)) rfl ?_ ?_
    · rw [Dyadic.mem_shift_toSet]
      have := Dyadic.mem_toSet (I := IT) (x := y - ((-1 : ℤ) : ℝ) * IT.length)
      refine this.2 ⟨?_, ?_⟩ <;> push_cast <;> linarith [hy3.1]
    · intro z hz
      rw [Dyadic.mem_shift_toSet] at hz
      obtain ⟨hz1, hz2⟩ := hz
      push_cast at hz1 hz2
      constructor <;> linarith
  · by_cases h2 : y < IT.right
    · refine key IT rfl ⟨not_lt.1 h1, h2⟩ ?_
      intro z hz
      constructor <;> linarith [hz.1, hz.2]
    · refine key (IT.shift 1) rfl ?_ ?_
      · rw [Dyadic.mem_shift_toSet]
        refine ⟨?_, ?_⟩ <;> push_cast <;> linarith [hy3.2, not_lt.1 h2]
      · intro z hz
        rw [Dyadic.mem_shift_toSet] at hz
        obtain ⟨hz1, hz2⟩ := hz
        push_cast at hz1 hz2
        have := IT.right_eq
        constructor <;> linarith

/-! ### The mass of `F` in the Calderón–Zygmund intervals -/

/-- If `x₀ ∈ I_T` and `x₀ ∉ Ω_λ`, then `|F ∩ J| ≤ 3λ|J|` for every
`J ∈ czFam` inside `3 I_T`. -/
theorem volume_inter_czFam_le (hF : MeasurableSet F) (hlam : 0 ≤ lam) {x₀ : ℝ}
    (hx₀ : x₀ ∈ IT.toSet) (hx₀Ω : x₀ ∉ maxSuperlevel F lam) {J : Dyadic}
    (hJ : J ∈ czFam F lam IT) (hJ3 : J.toSet ⊆ IT.dilate 3) :
    volume (F ∩ J.toSet) ≤ ENNReal.ofReal (3 * lam * J.length) := by
  have hJk := czFam_k_le hJ
  have hL := IT.length_pos
  rcases hJk.lt_or_eq with hlt | heq
  · -- the parent is not inside `Ω_λ`: it contains a point `y ∉ Ω_λ`
    have hpar : ¬ J.parent.toSet ⊆ maxSuperlevel F lam := by
      intro hsub
      have hp : czProp F lam IT J.parent := ⟨hsub, by simp only [Dyadic.parent_k]; omega⟩
      have := hJ.2 J.parent hp J.toSet_subset_parent
      have hk := congrArg Dyadic.k this
      simp only [Dyadic.parent_k] at hk
      omega
    obtain ⟨y, hy, hyΩ⟩ := Set.not_subset.1 hpar
    have hP := J.parent.left_lt_right
    have h1 := volume_inter_Icc_le_of_notMem hF hlam hyΩ hy.1 hy.2.le hP
    calc volume (F ∩ J.toSet) ≤ volume (F ∩ Icc J.parent.left J.parent.right) := by
          refine measure_mono (inter_subset_inter_right _ ?_)
          intro z hz
          have := J.toSet_subset_parent hz
          exact ⟨this.1, this.2.le⟩
      _ ≤ ENNReal.ofReal (lam * (J.parent.right - J.parent.left)) := h1
      _ ≤ ENNReal.ofReal (3 * lam * J.length) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := J.parent.right_eq
          have := J.length_parent
          have := J.length_pos
          nlinarith
  · -- `|J| = |I_T|`
    have hlen : J.length = IT.length := Dyadic.length_eq_iff.2 heq
    have hc := IT.center_eq
    have hr := IT.right_eq
    have hxa : IT.left - IT.length ≤ x₀ := by linarith [hx₀.1]
    have hxb : x₀ ≤ IT.right + IT.length := by linarith [hx₀.2]
    have hab : IT.left - IT.length < IT.right + IT.length := by linarith
    have h1 := volume_inter_Icc_le_of_notMem hF hlam hx₀Ω hxa hxb hab
    calc volume (F ∩ J.toSet) ≤ volume (F ∩ Icc (IT.left - IT.length) (IT.right + IT.length)) := by
          refine measure_mono (inter_subset_inter_right _ ?_)
          intro z hz
          have := hJ3 hz
          rw [dilate_three_eq] at this
          exact ⟨this.1, this.2.le⟩
      _ ≤ ENNReal.ofReal (lam * ((IT.right + IT.length) - (IT.left - IT.length))) := h1
      _ = ENNReal.ofReal (3 * lam * J.length) := by
          congr 1; rw [hlen, hr]; ring

end PrimeCarleson.Proof.Oplus
