module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Disjointness

/-!
# The intervals `𝒥` of the proof of the tree estimate ([O+] L2081-L2165)

Source: [O+] `treeestimatesmallintervals`, L2081–L2091; [O+] `usedensitybound`, L2158–L2165;
[O+] `treeestimate`, L2127–L2135: "Let `𝒥` be
the collection of dyadic intervals `J` which are maximal with respect to the property that
`I ⊄ 3J` for every `P ∈ T`."

* `Dyadic.dist I J = max(0, J.left - I.right, I.left - J.right)` is `dist(I, J)`;
  `Dyadic.length_le_add_dist_of_not_subset_dilate` says `|J| ≤ |I| + dist(I, J)` when `I ⊄ 3J`,
  and `Dyadic.one_add_abs_sub_center_div_le` converts it into the comparison
  `1 + |x - c(I)|/|I| ≤ (5/2)(1 + dist(I, J)/|I|)` for `x ∈ J` (L2102-L2103).
* `MultitileTree.Avoids 𝒯 J` is the property `I ⊄ 3J` for all `P ∈ T`;
  `MultitileTree.IsMaxAvoiding 𝒯 J` says `J ∈ 𝒥`. Distinct elements of `𝒥` are disjoint
  (`IsMaxAvoiding.disjoint`), every point of `ℝ` lies in one (`exists_isMaxAvoiding_mem`, for a
  nonempty tree), and the elements meeting `16 I_𝒯` have total length at most `48 |I_𝒯|`
  (`sum_length_le`).
* `exists_nearby_tile_and_interval` is the nearby tile and interval of `usedensitybound`
  (L2158-L2165): a multitile `P* ∈ T` with `I* ⊂ 3 J̃` and a dyadic `J'` with `|J| ≤ |J'| ≤ 4|J|`,
  `I* ⊂ J'`. The printed `dist(J, J') ≤ |J|` is replaced by the form the density step uses: every
  `x ∈ J` has `|x - c(J')| ≤ (9/2)|J'|` (the printed distance bound holds only with `2|J|`).
* `exists_far_bounds`: for `ℓ ≥ 4` and `J ∈ 𝒥` meeting `ℝ ∖ 2^ℓ I_𝒯` one has
  `((2^ℓ - 1)/8) |I_𝒯| ≤ |J|` and `|J| ≤ 3 dist(I_𝒯, J)` (L2128-L2130, with slightly different
  constants).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### The distance between dyadic intervals -/

namespace Dyadic

/-- `dist(I, J) = max(0, J.left - I.right, I.left - J.right)`, the distance between the
half-open intervals `I` and `J`. -/
def dist (I J : Dyadic) : ℝ := max 0 (max (J.left - I.right) (I.left - J.right))

/-- The distance is nonnegative. -/
theorem dist_nonneg (I J : Dyadic) : 0 ≤ I.dist J := le_max_left _ _

/-- `J.left - I.right ≤ dist(I, J)`. -/
theorem sub_le_dist (I J : Dyadic) : J.left - I.right ≤ I.dist J :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- `I.left - J.right ≤ dist(I, J)`. -/
theorem sub_le_dist' (I J : Dyadic) : I.left - J.right ≤ I.dist J :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- Two points of `I` and `J` are at distance at least `dist(I, J)`. -/
theorem dist_le_abs_sub {I J : Dyadic} {x y : ℝ} (hx : x ∈ I.toSet) (hy : y ∈ J.toSet) :
    I.dist J ≤ |x - y| := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine max_le (abs_nonneg _) (max_le ?_ ?_)
  · calc J.left - I.right ≤ y - x := by linarith
      _ ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
  · calc I.left - J.right ≤ x - y := by linarith
      _ ≤ |x - y| := le_abs_self _

/-- A point `x ∈ J` is at distance `≤ dist(I, J) + |I|/2 + |J|` from the centre of `I`. -/
theorem abs_sub_center_le_dist {I J : Dyadic} {x : ℝ} (hx : x ∈ J.toSet) :
    |x - I.center| ≤ I.dist J + I.length / 2 + J.length := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 := sub_le_dist I J
  have h2 := sub_le_dist' I J
  have e1 := I.right_eq
  have e2 := J.right_eq
  have e3 := I.center_eq
  rw [abs_le]
  constructor <;> linarith

/-- `dist(I, J) ≤ |x - c(I)|` for `x ∈ J`. -/
theorem dist_le_abs_sub_center {I J : Dyadic} {x : ℝ} (hx : x ∈ J.toSet) :
    I.dist J ≤ |I.center - x| := dist_le_abs_sub I.center_mem_toSet hx

/-- **`I ⊄ 3J` forces `|J| ≤ |I| + dist(I, J)`** (L2102-L2103). -/
theorem length_le_add_dist_of_not_subset_dilate {I J : Dyadic} (h : ¬ I.toSet ⊆ J.dilate 3) :
    J.length ≤ I.length + I.dist J := by
  rw [Set.not_subset] at h
  obtain ⟨y, hy, hyn⟩ := h
  obtain ⟨hy1, hy2⟩ := hy
  have h1 := sub_le_dist I J
  have h2 := sub_le_dist' I J
  have e1 := I.right_eq
  have e2 := J.right_eq
  have e3 := J.center_eq
  simp only [Dyadic.dilate, mem_Ico, not_and_or, not_le, not_lt] at hyn
  rcases hyn with h | h <;> linarith

/-- **For `x ∈ J` and `I ⊄ 3J`:** `1 + |x - c(I)|/|I| ≤ (5/2)(1 + dist(I, J)/|I|)`
(L2102-L2103: "`1 + |x - y|/|I| ≤ C(1 + dist(I, J)/|I|)`"). -/
theorem one_add_abs_sub_center_div_le {I J : Dyadic} {x : ℝ} (hx : x ∈ J.toSet)
    (h : ¬ I.toSet ⊆ J.dilate 3) :
    1 + |x - I.center| / I.length ≤ 5 / 2 * (1 + I.dist J / I.length) := by
  have hI := I.length_pos
  have h1 := abs_sub_center_le_dist (I := I) hx
  have h2 := length_le_add_dist_of_not_subset_dilate h
  have h3 : |x - I.center| / I.length ≤ 3 / 2 + 2 * (I.dist J / I.length) := by
    rw [div_le_iff₀ hI]
    have : (3 / 2 + 2 * (I.dist J / I.length)) * I.length = 3 / 2 * I.length + 2 * I.dist J := by
      field_simp
    rw [this]
    linarith
  have h4 : 0 ≤ I.dist J / I.length := div_nonneg (I.dist_nonneg J) hI.le
  linarith

/-- For `x ∈ J`: `1 + dist(I, J)/|I| ≤ 1 + |x - c(I)|/|I|`. -/
theorem one_add_dist_div_le {I J : Dyadic} {x : ℝ} (hx : x ∈ J.toSet) :
    1 + I.dist J / I.length ≤ 1 + |x - I.center| / I.length := by
  have hI := I.length_pos
  have h1 := dist_le_abs_sub_center (I := I) hx
  rw [abs_sub_comm] at h1
  have : I.dist J / I.length ≤ |x - I.center| / I.length := by gcongr
  linarith

/-- A dyadic interval inside `J.dilate 3` has length at most `3|J|`. -/
theorem length_le_of_subset_dilate_three {I J : Dyadic} (h : I.toSet ⊆ J.dilate 3) :
    I.length ≤ 3 * J.length := by
  obtain ⟨h1, h2⟩ := (Set.Ico_subset_Ico_iff I.left_lt_right).1 h
  have := I.right_eq
  have := J.center_eq
  linarith

/-- `[x - |J|, x + |J|) ⊆ 3J` for `x ∈ J`. -/
theorem Ico_subset_dilate_three {J : Dyadic} {x : ℝ} (hx : x ∈ J.toSet) :
    Ico (x - J.length) (x + J.length) ⊆ J.dilate 3 := by
  obtain ⟨h1, h2⟩ := hx
  have := J.right_eq
  have := J.center_eq
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  rw [Dyadic.mem_dilate]
  constructor <;> linarith

/-- `3 J̃ = [a - 2|J|, a + 4|J|)` for the dyadic parent `J̃ = [a, a + 2|J|)` of `J`. -/
theorem parent_dilate_three (J : Dyadic) :
    J.parent.dilate 3 = Ico (J.parent.left - J.length * 2) (J.parent.left + J.length * 4) := by
  unfold Dyadic.dilate
  rw [J.parent.center_eq, J.length_parent]
  congr 1 <;> ring

end Dyadic

/-! ### The collection `𝒥` -/

namespace MultitileTree

variable {ρ : Idx} (𝒯 : MultitileTree ρ)

/-- `J` has the property `I ⊄ 3J` for every `P ∈ T` (L2081). -/
def Avoids (J : Dyadic) : Prop := ∀ P ∈ 𝒯.T, ¬ P.I.toSet ⊆ J.dilate 3

/-- `J ∈ 𝒥`: `J` is maximal (for inclusion) among the dyadic intervals with `I ⊄ 3J` for every
`P ∈ T` (L2081). -/
def IsMaxAvoiding (J : Dyadic) : Prop :=
  𝒯.Avoids J ∧ ∀ J' : Dyadic, 𝒯.Avoids J' → J.toSet ⊆ J'.toSet → J' = J

variable {𝒯}

/-- Distinct elements of `𝒥` are disjoint. -/
theorem IsMaxAvoiding.disjoint {J₁ J₂ : Dyadic} (h₁ : 𝒯.IsMaxAvoiding J₁)
    (h₂ : 𝒯.IsMaxAvoiding J₂) (hne : J₁ ≠ J₂) : Disjoint J₁.toSet J₂.toSet := by
  rcases J₁.nested_or_disjoint J₂ with h | h | h
  · exact absurd (h₁.2 J₂ h₂.1 h).symm hne
  · exact absurd (h₂.2 J₁ h₁.1 h) hne
  · exact h

/-- **Every point lies in some `J ∈ 𝒥`** (for a nonempty finite tree). -/
theorem exists_isMaxAvoiding_mem (hne : 𝒯.T.Nonempty) (x : ℝ) :
    ∃ J, 𝒯.IsMaxAvoiding J ∧ x ∈ J.toSet := by
  classical
  -- small intervals avoid
  obtain ⟨kmin, hkmin⟩ : ∃ k : ℤ, ∀ P ∈ 𝒯.T, k ≤ P.I.k :=
    (𝒯.T.image fun P => P.I.k).bddBelow.imp fun b hb P hP => hb (Finset.mem_image_of_mem _ hP)
  have hsmall : 𝒯.Avoids (Dyadic.ofPoint (kmin - 2) x) := by
    intro P hP hsub
    have h1 := Dyadic.length_le_of_subset_dilate_three hsub
    have h2 : (2 : ℝ) ^ (kmin - 2) * 4 = (2 : ℝ) ^ kmin := by
      rw [zpow_sub₀ (by norm_num)]; ring
    have h3 : (2 : ℝ) ^ kmin ≤ P.I.length := zpow_le_zpow_right₀ (by norm_num) (hkmin P hP)
    have h4 : (Dyadic.ofPoint (kmin - 2) x).length = (2 : ℝ) ^ (kmin - 2) := rfl
    rw [h4] at h1
    nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (kmin - 2)]
  -- large intervals do not avoid
  obtain ⟨P₀, hP₀⟩ := hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max |x - P₀.I.left| |P₀.I.right - x|)
    (by norm_num : (1 : ℝ) < 2)
  have hbdd : ∀ k : ℤ, 𝒯.Avoids (Dyadic.ofPoint k x) → k ≤ n := by
    intro k hk
    by_contra hkn
    rw [not_le] at hkn
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ k := by
      rw [← zpow_natCast]; exact zpow_le_zpow_right₀ (by norm_num) hkn.le
    have hmem := Dyadic.mem_toSet_ofPoint k x
    have hsub := Dyadic.Ico_subset_dilate_three hmem
    refine hk P₀ hP₀ ?_
    refine Set.Subset.trans ?_ hsub
    have hl : (Dyadic.ofPoint k x).length = (2 : ℝ) ^ k := rfl
    rw [hl]
    have h1 : |x - P₀.I.left| ≤ (2 : ℝ) ^ k :=
      (le_max_left _ _).trans (hn.le.trans hpow)
    have h2 : |P₀.I.right - x| ≤ (2 : ℝ) ^ k :=
      (le_max_right _ _).trans (hn.le.trans hpow)
    rw [abs_le] at h1 h2
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have := P₀.I.left_lt_right
    rw [Set.mem_Ico]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨kmax, hkmax, hkmax'⟩ := Int.exists_greatest_of_bdd
    (P := fun k : ℤ => 𝒯.Avoids (Dyadic.ofPoint k x)) ⟨n, hbdd⟩ ⟨kmin - 2, hsmall⟩
  refine ⟨Dyadic.ofPoint kmax x, ⟨hkmax, fun J' hJ' hsub => ?_⟩, Dyadic.mem_toSet_ofPoint kmax x⟩
  have hx' : x ∈ J'.toSet := hsub (Dyadic.mem_toSet_ofPoint kmax x)
  have hJ'eq : J' = Dyadic.ofPoint J'.k x := Dyadic.eq_ofPoint_of_mem hx'
  have h1 : J'.k ≤ kmax := hkmax' J'.k (by rw [← hJ'eq]; exact hJ')
  have h2 : kmax ≤ J'.k := Dyadic.k_le_of_toSet_subset hsub
  rw [hJ'eq, show J'.k = kmax from le_antisymm h1 h2]

/-- **The nearby tile and interval** ([O+] L2158-L2165). If `J ∈ 𝒥` there is `P* = (I*, ω_u*) ∈ T`
with `I* ⊂ 3 J̃` (`J̃` the dyadic parent of `J`) and a dyadic `J'` with `|J| ≤ |J'| ≤ 4|J|`,
`I* ⊂ J'` and `|x - c(J')| ≤ (9/2)|J'|` for all `x ∈ J`. -/
theorem exists_nearby_tile_and_interval {J : Dyadic} (hJ : 𝒯.IsMaxAvoiding J) :
    ∃ P ∈ 𝒯.T, P.I.toSet ⊆ J.parent.dilate 3 ∧ ∃ J' : Dyadic,
      J.length ≤ J'.length ∧ J'.length ≤ 4 * J.length ∧ P.I.toSet ⊆ J'.toSet ∧
        ∀ x ∈ J.toSet, |x - J'.center| ≤ 9 / 2 * J'.length := by
  -- the parent of `J` does not avoid
  have hpar : ¬ 𝒯.Avoids J.parent := by
    intro h
    have := hJ.2 J.parent h (J.toSet_subset_parent)
    have h1 := congrArg Dyadic.k this
    simp at h1
  simp only [Avoids, not_forall, not_not] at hpar
  obtain ⟨P, hP, hPsub⟩ := hpar
  refine ⟨P, hP, hPsub, ?_⟩
  have hjl : J.parent.length = 2 * J.length := Dyadic.length_parent J
  have hJsub : J.toSet ⊆ J.parent.toSet := J.toSet_subset_parent
  -- `3 J̃ = [a - 2j, a + 4j)` where `J̃ = [a, a + 2j)`
  have hdil := Dyadic.parent_dilate_three J
  have hpr := J.parent.right_eq
  rw [hjl] at hpr
  -- choose `J'`
  have hIlen : P.I.length ≤ 6 * J.length := by
    rw [hdil] at hPsub
    obtain ⟨h1, h2⟩ := (Set.Ico_subset_Ico_iff P.I.left_lt_right).1 hPsub
    have := P.I.right_eq
    linarith
  have hIk : P.I.k ≤ J.k + 2 := by
    by_contra hk
    rw [not_le] at hk
    have h1 : (2 : ℝ) ^ (J.k + 3) ≤ (2 : ℝ) ^ P.I.k := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (J.k + 3) = 8 * (2 : ℝ) ^ J.k := by
      rw [zpow_add₀ (by norm_num)]; ring
    have h3 : P.I.length = (2 : ℝ) ^ P.I.k := rfl
    have h4 : J.length = (2 : ℝ) ^ J.k := rfl
    have := J.length_pos
    linarith
  -- a point of `I*`
  have hz : P.I.left ∈ J.parent.dilate 3 := hPsub P.I.left_mem_toSet
  by_cases hcase : J.length ≤ P.I.length
  · refine ⟨P.I, hcase, ?_, subset_rfl, ?_⟩
    · have : P.I.length = (2 : ℝ) ^ P.I.k := rfl
      have h2 : (2 : ℝ) ^ P.I.k ≤ (2 : ℝ) ^ (J.k + 2) := zpow_le_zpow_right₀ (by norm_num) hIk
      have h3 : (2 : ℝ) ^ (J.k + 2) = 4 * J.length := by
        unfold Dyadic.length; rw [zpow_add₀ (by norm_num)]; ring
      linarith
    · intro x hx
      rw [hdil] at hz
      obtain ⟨hz1, hz2⟩ := hz
      have hxm : J.parent.left ≤ x ∧ x < J.parent.right := hJsub hx
      have hl2 : P.I.length ≤ 4 * J.length := by
        have : P.I.length = (2 : ℝ) ^ P.I.k := rfl
        have h2 : (2 : ℝ) ^ P.I.k ≤ (2 : ℝ) ^ (J.k + 2) := zpow_le_zpow_right₀ (by norm_num) hIk
        have h3 : (2 : ℝ) ^ (J.k + 2) = 4 * J.length := by
          unfold Dyadic.length; rw [zpow_add₀ (by norm_num)]; ring
        linarith
      have := P.I.length_pos
      have hcen := P.I.center_eq
      rw [abs_le]
      constructor <;> nlinarith
  · rw [not_le] at hcase
    set J' : Dyadic := Dyadic.ofPoint J.k P.I.left with hJ'
    have hJ'len : J'.length = J.length := rfl
    have hsubJ' : P.I.toSet ⊆ J'.toSet := by
      refine Dyadic.toSet_subset_of_length_le_of_not_disjoint (by rw [hJ'len]; exact hcase.le) ?_
      rw [Set.not_disjoint_iff]
      exact ⟨P.I.left, P.I.left_mem_toSet, Dyadic.mem_toSet_ofPoint J.k P.I.left⟩
    refine ⟨J', by rw [hJ'len], by rw [hJ'len]; linarith [J.length_pos], hsubJ', ?_⟩
    intro x hx
    rw [hdil] at hz
    obtain ⟨hz1, hz2⟩ := hz
    have hxm : J.parent.left ≤ x ∧ x < J.parent.right := hJsub hx
    have hpt : P.I.left ∈ J'.toSet := Dyadic.mem_toSet_ofPoint J.k P.I.left
    have hc := Dyadic.abs_sub_center_le hpt
    rw [hJ'len] at hc ⊢
    have := J.length_pos
    rw [abs_le] at hc ⊢
    constructor <;> nlinarith [hc.1, hc.2]

/-- `J ∈ 𝒥` meeting `16 I_𝒯` has `|J| < 16 |I_𝒯|` (otherwise `3J` contains `I_𝒯`). -/
theorem IsMaxAvoiding.length_lt {J : Dyadic} (hJ : 𝒯.IsMaxAvoiding J) (hne : 𝒯.T.Nonempty)
    (htime : ∀ P ∈ 𝒯.T, P.I.toSet ⊆ 𝒯.I.toSet) (hmeet : (J.toSet ∩ 𝒯.I.dilate 16).Nonempty) :
    J.length < 16 * 𝒯.I.length := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨y, hyJ, hy16⟩ := hmeet
  obtain ⟨P, hP⟩ := hne
  refine hJ.1 P hP ?_
  refine (htime P hP).trans (Set.Subset.trans ?_ (Dyadic.Ico_subset_dilate_three hyJ))
  rw [Dyadic.mem_dilate] at hy16
  have e1 := 𝒯.I.center_eq
  have e2 := 𝒯.I.right_eq
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [Set.mem_Ico]
  constructor <;> nlinarith [hy16.1, hy16.2]

/-- **The elements of `𝒥` meeting `16 I_𝒯` have total length at most `48 |I_𝒯|`** (they are
disjoint, of length `< 16 |I_𝒯|`, and lie in `[c - 24|I_𝒯|, c + 24|I_𝒯|)`). -/
theorem sum_length_le (hne : 𝒯.T.Nonempty) (htime : ∀ P ∈ 𝒯.T, P.I.toSet ⊆ 𝒯.I.toSet)
    (𝒥s : Finset Dyadic)
    (h𝒥 : ∀ J ∈ 𝒥s, 𝒯.IsMaxAvoiding J ∧ (J.toSet ∩ 𝒯.I.dilate 16).Nonempty) :
    ∑ J ∈ 𝒥s, J.length ≤ 48 * 𝒯.I.length := by
  have hdisj : Set.PairwiseDisjoint (𝒥s : Set Dyadic) (fun J => J.toSet) :=
    fun J hJ J' hJ' hne' => (h𝒥 J hJ).1.disjoint (h𝒥 J' hJ').1 hne'
  have hsub : (⋃ J ∈ 𝒥s, J.toSet) ⊆ Ico (𝒯.I.center - 24 * 𝒯.I.length)
      (𝒯.I.center + 24 * 𝒯.I.length) := by
    intro z hz
    obtain ⟨J, hJ, hzJ⟩ := Set.mem_iUnion₂.1 hz
    obtain ⟨hJmax, y, hyJ, hy16⟩ := h𝒥 J hJ
    have hlt := hJmax.length_lt hne htime ⟨y, hyJ, hy16⟩
    rw [Dyadic.mem_dilate] at hy16
    have e2 := J.right_eq
    obtain ⟨hy1, hy2⟩ := hyJ
    obtain ⟨hz1, hz2⟩ := hzJ
    rw [Set.mem_Ico]
    constructor <;> linarith [hy16.1, hy16.2]
  have h1 := measureReal_biUnion_finset (μ := volume) hdisj
    (fun J _ => J.measurableSet_toSet) (fun J _ => by simp [Dyadic.volume_toSet])
  have h2 : volume.real (⋃ J ∈ 𝒥s, J.toSet) ≤ volume.real (Ico (𝒯.I.center - 24 * 𝒯.I.length)
      (𝒯.I.center + 24 * 𝒯.I.length)) := measureReal_mono hsub (by simp)
  rw [h1] at h2
  simp only [Dyadic.volume_real_toSet] at h2
  have h3 : volume.real (Ico (𝒯.I.center - 24 * 𝒯.I.length) (𝒯.I.center + 24 * 𝒯.I.length)) =
      48 * 𝒯.I.length := by
    have := 𝒯.I.length_pos
    rw [Real.volume_real_Ico_of_le (by linarith)]
    ring
  linarith

/-- **Geometry of `J ∈ 𝒥` far from the top** (L2128-L2130). If `ℓ ≥ 4` and `J ∈ 𝒥` meets
`ℝ ∖ 2^ℓ I_𝒯`, then `(2^ℓ/2 - 1/2)|I_𝒯| ≤ 4|J|` and `|J| ≤ 3 dist(I_𝒯, J)`. -/
theorem exists_far_bounds {J : Dyadic} (hJ : 𝒯.IsMaxAvoiding J)
    (htime : ∀ P ∈ 𝒯.T, P.I.toSet ⊆ 𝒯.I.toSet) {ℓ : ℕ} (hℓ : 4 ≤ ℓ)
    (hmeet : (J.toSet ∩ (𝒯.I.dilate ((2 : ℝ) ^ ℓ))ᶜ).Nonempty) :
    ((2 : ℝ) ^ ℓ / 2 - 1 / 2) * 𝒯.I.length ≤ 4 * J.length ∧ J.length ≤ 3 * 𝒯.I.dist J := by
  obtain ⟨y, hyJ, hyc⟩ := hmeet
  obtain ⟨P, hP, hsub3, -⟩ := exists_nearby_tile_and_interval hJ
  have hz : P.I.left ∈ 𝒯.I.toSet := htime P hP P.I.left_mem_toSet
  have hz3 := hsub3 P.I.left_mem_toSet
  rw [Dyadic.parent_dilate_three] at hz3
  obtain ⟨hz31, hz32⟩ := hz3
  have hyp := J.toSet_subset_parent hyJ
  have h1 := Dyadic.half_le_abs_of_not_mem_dilate hyc
  have h2 := Dyadic.abs_sub_center_le hz
  have hpr := J.parent.right_eq
  rw [J.length_parent] at hpr
  have hpow : (16 : ℝ) ≤ (2 : ℝ) ^ ℓ := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  have hIT := 𝒯.I.length_pos
  have hJl := J.length_pos
  have habs : |y - 𝒯.I.center| ≤ |y - P.I.left| + |P.I.left - 𝒯.I.center| := by
    have := abs_add_le (y - P.I.left) (P.I.left - 𝒯.I.center)
    simpa using this
  have hyz : |y - P.I.left| ≤ 4 * J.length := by
    rw [abs_le]
    obtain ⟨hy1, hy2⟩ := hyp
    constructor <;> linarith
  have hfirst : ((2 : ℝ) ^ ℓ / 2 - 1 / 2) * 𝒯.I.length ≤ 4 * J.length := by
    nlinarith
  refine ⟨hfirst, ?_⟩
  -- `I_𝒯 ⊄ 3J`
  have hnot : ¬ 𝒯.I.toSet ⊆ J.dilate 3 := fun h => hJ.1 P hP ((htime P hP).trans h)
  have h3 := Dyadic.length_le_add_dist_of_not_subset_dilate hnot
  nlinarith

end MultitileTree

end PrimeCarleson.Proof.Oplus
