module

public import PrimeCarleson.Proof.Oplus.Defs.Index
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Int.LeastGreatest

/-!
# Whitney intervals `𝒥_{ξ,ξ'}` and their classes ([O+] L938-L964, L1040-L1057)

[O+] L938-L941: "For any `ξ < ξ'`, let `𝒥_{ξ,ξ'}` be the set
of maximal dyadic intervals `J` such that `J ⊂ (ξ,ξ')` and `dis(J,ξ) ≥ |J|`, `dis(J,ξ') ≥ |J|`";
L961-L964: "for each `J ∈ 𝒥_{ξ,ξ'}`, one may check that there is a unique interval
`J' ∈ 𝒥_{ξ,ξ'}` which lies strictly to the left of `J` and satisfies `dis(J',J) = 0`, and one may
check that `J'` has size `|J|/2, |J|, 2|J|`"; L1054-L1057: the sorting of `𝒥_{ξ,ξ'}` into the ten
classes `𝒥_{ξ,ξ',ρ}`, `ρ ∈ R`. Source: [O+], L938–L964; [O+], L1040–L1057 (the half that
`Defs/Index.lean` leaves open: the covering of `𝒥_{ξ,ξ'}` by the
classes and the size ratio `2^{i(ρ)}`); both are asserted in the paper with "one may check".

* `Dyadic.Admissible ξ ξ' J` and `Dyadic.IsWhitney ξ ξ' J` (`J ∈ 𝒥_{ξ,ξ'}`): for `J = [a, b)`,
  `J ⊂ (ξ, ξ')`, `dis(J, ξ) = a - ξ ≥ |J|` and `dis(J, ξ') = ξ' - b ≥ |J|` read
  `ξ + |J| ≤ a` and `b + |J| ≤ ξ'`;
* `Dyadic.exists_isWhitney_mem`: every point of `(ξ, ξ')` lies in a Whitney interval;
  `IsWhitney.eq_or_disjoint`: Whitney intervals are nested-free, hence pairwise disjoint;
* `IsWhitney.comparable`, `IsWhitney.left_eq_right_of_gap` (the *gap lemma*: Whitney intervals at
  distance `< |J|/50` are adjacent), `IsWhitney.exists_left_nbr`, `exists_right_nbr`,
  `eq_of_right_eq` (uniqueness of `J'`), `nbr_k` (`|J'| ∈ {|J|/2, |J|, 2|J|}`);
* `nbrIdx ξ ξ' J = i(J)` with `|J'| = 2^{i(J)} |J|` (`nbrIdx_mem`: `i(J) ∈ {-1, 0, 1}`);
* the classes (for `ξ` outside the dyadic end points `n 2^m`, the standing assumption of
  L897-L899): `IsWhitney.exists_inClass` (`𝒥_{ξ,ξ'} ⊆ ⋃_{ρ ∈ R} 𝒥_{ξ,ξ',ρ}`),
  `isWhitney_of_inClass` (the converse), `IsWhitney.existsUnique_inClass`, `nbrIdx_of_inClass`
  (`i(J) = i(ρ)`).
  Only the end point `ξ` matters: the convention `ξ ∈ J - (m+1)|J|` makes the position `a - ξ`
  of the classes half-open on the side of `ξ`, where Whitney maximality can flip at a dyadic
  point, whereas `ξ' ∈ J + (n+1)|J|` and `dis(ξ', J) ≥ n|J|` are closed on the left.
-/

@[expose] public noncomputable section

open MeasureTheory Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

namespace Dyadic

variable (I : Dyadic)

/-- `I ⊆ J` forces the left end point of `J` to be at most the left end point of `I`. -/
theorem left_le_left_of_subset {I J : Dyadic} (h : I.toSet ⊆ J.toSet) : J.left ≤ I.left :=
  (h I.left_mem_toSet).1

/-- `I ⊆ J` forces the right end point of `I` to be at most the right end point of `J`. -/
theorem right_le_right_of_subset {I J : Dyadic} (h : I.toSet ⊆ J.toSet) : I.right ≤ J.right := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : J.right ∈ I.toSet := ⟨(h I.left_mem_toSet).2.le, hlt⟩
  exact lt_irrefl _ (h h1).2

/-- `I ⊆ J` forces `|I| ≤ |J|`. -/
theorem length_le_of_subset {I J : Dyadic} (h : I.toSet ⊆ J.toSet) : I.length ≤ J.length := by
  have h1 := right_le_right_of_subset h
  have h2 := left_le_left_of_subset h
  rw [right_eq, right_eq] at h1
  linarith

/-- The parent contains the interval: `parent.left ≤ left`. -/
theorem parent_left_le : I.parent.left ≤ I.left := left_le_left_of_subset I.toSet_subset_parent

/-- The parent contains the interval: `right ≤ parent.right`. -/
theorem le_parent_right : I.right ≤ I.parent.right := right_le_right_of_subset I.toSet_subset_parent

/-- `left - |I| ≤ parent.left`. -/
theorem left_sub_length_le_parent_left : I.left - I.length ≤ I.parent.left := by
  have h1 := I.le_parent_right
  have h2 := I.parent.right_eq
  have h3 := I.right_eq
  have h4 := I.length_parent
  linarith

/-- `parent.right ≤ right + |I|`. -/
theorem parent_right_le : I.parent.right ≤ I.right + I.length := by
  have h1 := I.parent_left_le
  have h2 := I.parent.right_eq
  have h3 := I.right_eq
  have h4 := I.length_parent
  linarith

/-! ### Admissible intervals -/

/-- `J` is *admissible* for `(ξ, ξ')` if `J ⊂ (ξ, ξ')`, `dist(J, ξ) ≥ |J|` and `dist(J, ξ') ≥ |J|`
([O+] L938-L941). For `J = [a, b)` the three conditions say `ξ + |J| ≤ a` and `b + |J| ≤ ξ'`
(then `J ⊂ (ξ, ξ')` and the distances are `a - ξ` and `ξ' - b`). -/
def Admissible (ξ ξ' : ℝ) (J : Dyadic) : Prop :=
  ξ + J.length ≤ J.left ∧ J.right + J.length ≤ ξ'

variable {ξ ξ' η : ℝ} {J K : Dyadic}

/-- A sub-interval of an admissible interval is admissible. -/
theorem Admissible.of_subset (hK : K.Admissible ξ ξ') (h : J.toSet ⊆ K.toSet) :
    J.Admissible ξ ξ' := by
  have h1 := left_le_left_of_subset h
  have h2 := right_le_right_of_subset h
  have h3 := length_le_of_subset h
  exact ⟨by linarith [hK.1], by linarith [hK.2]⟩

/-- The maximal admissible dyadic intervals `𝒥_{ξ,ξ'}` of [O+] L938-L941: `J` is admissible and
every admissible dyadic interval containing `J` is `J`. -/
def IsWhitney (ξ ξ' : ℝ) (J : Dyadic) : Prop :=
  J.Admissible ξ ξ' ∧ ∀ K : Dyadic, K.Admissible ξ ξ' → J.toSet ⊆ K.toSet → K = J

/-- `J` is maximal admissible iff it is admissible and its parent is not. -/
theorem isWhitney_iff : J.IsWhitney ξ ξ' ↔ J.Admissible ξ ξ' ∧ ¬ J.parent.Admissible ξ ξ' := by
  constructor
  · rintro ⟨hA, hM⟩
    refine ⟨hA, fun hP => ?_⟩
    have := hM _ hP J.toSet_subset_parent
    have h2 : J.parent.length = J.length := by rw [this]
    rw [length_parent] at h2
    linarith [J.length_pos]
  · rintro ⟨hA, hP⟩
    refine ⟨hA, fun K hK hJK => ?_⟩
    have hk := k_le_of_toSet_subset hJK
    rcases hk.eq_or_lt with hk | hk
    · exact (eq_of_toSet_subset_of_k_eq hk hJK).symm
    · exfalso
      refine hP (Admissible.of_subset hK ?_)
      have hk' : J.parent.k ≤ K.k := by simpa using Int.add_one_le_iff.2 hk
      rcases toSet_subset_or_disjoint_of_k_le J.parent K hk' with h | h
      · exact h
      · exfalso
        exact Set.disjoint_left.1 h (J.toSet_subset_parent J.left_mem_toSet) (hJK J.left_mem_toSet)

/-- The parent of a Whitney interval is not admissible. -/
theorem IsWhitney.not_admissible_parent (h : J.IsWhitney ξ ξ') : ¬ J.parent.Admissible ξ ξ' :=
  (isWhitney_iff.1 h).2

/-- Distinct Whitney intervals of `(ξ, ξ')` are disjoint. -/
theorem IsWhitney.eq_or_disjoint (hJ : J.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ') :
    J = K ∨ Disjoint J.toSet K.toSet := by
  rcases nested_or_disjoint J K with h | h | h
  · exact Or.inl (hJ.2 K hK.1 h).symm
  · exact Or.inl (hK.2 J hJ.1 h)
  · exact Or.inr h

/-! ### Existence: every point of `(ξ, ξ')` lies in a Whitney interval -/

theorem exists_isWhitney_mem (h : η ∈ Ioo ξ ξ') :
    ∃ J : Dyadic, J.IsWhitney ξ ξ' ∧ η ∈ J.toSet := by
  classical
  have hδ : 0 < min (η - ξ) (ξ' - η) := lt_min (by linarith [h.1]) (by linarith [h.2])
  -- nonemptiness: some small scale is admissible
  have hne : ∃ k : ℤ, (ofPoint k η).Admissible ξ ξ' := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hδ) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨-(n : ℤ) - 1, ?_⟩
    have hm := mem_toSet_ofPoint (-(n : ℤ) - 1) η
    have hlen : (ofPoint (-(n : ℤ) - 1) η).length = (1 / 2 : ℝ) ^ n / 2 := by
      unfold length ofPoint
      simp only
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg, zpow_natCast, zpow_one, one_div_pow]
      ring
    have h1 := min_le_left (η - ξ) (ξ' - η)
    have h2 := min_le_right (η - ξ) (ξ' - η)
    have hr := right_eq (ofPoint (-(n : ℤ) - 1) η)
    constructor <;> nlinarith [hm.1, hm.2]
  -- boundedness of the admissible scales
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, (ofPoint k η).Admissible ξ ξ' → k ≤ b := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (ξ' - ξ) (by norm_num : (1 : ℝ) < 2)
    refine ⟨N, fun k hk => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (2 : ℝ) ^ (N : ℤ) < 2 ^ k := zpow_lt_zpow_right₀ (by norm_num) hlt
    have h2 := right_eq (ofPoint k η)
    have h3 : (ofPoint k η).length = 2 ^ k := rfl
    have hL := (ofPoint k η).length_pos
    have : (2 : ℝ) ^ (N : ℤ) = 2 ^ N := zpow_natCast _ _
    linarith [hk.1, hk.2]
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨ofPoint k η, ⟨hk, fun K hK hJK => ?_⟩, mem_toSet_ofPoint k η⟩
  have hη : η ∈ K.toSet := hJK (mem_toSet_ofPoint k η)
  have hKeq : K = ofPoint K.k η := eq_ofPoint_of_mem hη
  have hKk : K.k ≤ k := hmax K.k (hKeq ▸ hK)
  have hkK : k ≤ K.k := k_le_of_toSet_subset hJK
  exact (eq_of_toSet_subset_of_k_eq (le_antisymm hkK hKk) hJK).symm

/-! ### Comparability of Whitney intervals -/

/-- A Whitney interval is within a factor `3` of its walls: its parent fails to be admissible. -/
theorem IsWhitney.wall_lt (hJ : J.IsWhitney ξ ξ') :
    J.left - ξ < 3 * J.length ∨ ξ' - J.right < 3 * J.length := by
  have hP := hJ.not_admissible_parent
  unfold Admissible at hP
  rw [not_and_or, not_le, not_le] at hP
  have h1 := J.left_sub_length_le_parent_left
  have h2 := J.parent_right_le
  have h3 := J.length_parent
  rcases hP with h | h
  · left; linarith
  · right; linarith

/-- **Comparability**: if `J` lies to the left of `K` with a gap `g = K.left - J.right ≥ 0`,
then `|J| - g < 4|K|` and `|K| - g < 4|J|`. -/
theorem IsWhitney.comparable (hJ : J.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ')
    (h : J.right ≤ K.left) :
    J.length - (K.left - J.right) < 4 * K.length ∧
      K.length - (K.left - J.right) < 4 * J.length := by
  have hL := J.length_pos
  have hLK := K.length_pos
  obtain ⟨hJ1, hJ2⟩ := hJ.1
  obtain ⟨hK1, hK2⟩ := hK.1
  have hJr := J.right_eq
  have hKr := K.right_eq
  constructor
  · rcases hK.wall_lt with w | w <;> linarith
  · rcases hJ.wall_lt with w | w <;> linarith

/-- The multiples of `2^k`: an integer multiple of `2^{k}` is an integer multiple of `2^{k'}` for
`k' ≤ k`. -/
theorem exists_int_mul_of_le {x : ℝ} {k k' : ℤ} (hk : k' ≤ k) (h : ∃ n : ℤ, x = 2 ^ k * n) :
    ∃ n : ℤ, x = 2 ^ k' * n := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨d, hd⟩ : ∃ d : ℕ, k = k' + d := ⟨(k - k').toNat, by omega⟩
  refine ⟨2 ^ d * n, ?_⟩
  rw [hd, zpow_add₀ (by norm_num)]
  push_cast
  simp
  ring

/-- The left end point is an integer multiple of `2^k`. -/
theorem exists_int_mul_left : ∃ n : ℤ, I.left = 2 ^ I.k * n := ⟨I.m, rfl⟩

/-- The right end point is an integer multiple of `2^k`. -/
theorem exists_int_mul_right : ∃ n : ℤ, I.right = 2 ^ I.k * n :=
  ⟨I.m + 1, by unfold right; push_cast; ring⟩

/-- If the right end point of `J` is at most the left end point of `K`, with a gap smaller than
both lengths, the gap is zero (end points of dyadic intervals are multiples of the shorter
length). -/
theorem left_eq_right_of_lt (h0 : J.right ≤ K.left) (h : K.left - J.right < J.length)
    (h' : K.left - J.right < K.length) : K.left = J.right := by
  obtain ⟨n₁, hn₁⟩ := exists_int_mul_of_le (min_le_left J.k K.k) (exists_int_mul_right J)
  obtain ⟨n₂, hn₂⟩ := exists_int_mul_of_le (min_le_right J.k K.k) (exists_int_mul_left K)
  have hpos : (0 : ℝ) < 2 ^ min J.k K.k := zpow_pos (by norm_num) _
  have hmin : (2 : ℝ) ^ min J.k K.k ≤ J.length ∨ (2 : ℝ) ^ min J.k K.k ≤ K.length := by
    rcases min_choice J.k K.k with hc | hc
    · left; rw [hc]; exact le_rfl
    · right; rw [hc]; exact le_rfl
  have hlt : K.left - J.right < 2 ^ min J.k K.k := by
    rcases le_total J.k K.k with hk | hk
    · rw [min_eq_left hk]; exact h
    · rw [min_eq_right hk]; exact h'
  have hd : K.left - J.right = 2 ^ min J.k K.k * ((n₂ - n₁ : ℤ) : ℝ) := by
    rw [hn₁, hn₂]; push_cast; ring
  have h1 : (0 : ℝ) ≤ ((n₂ - n₁ : ℤ) : ℝ) := by
    have : 0 ≤ K.left - J.right := sub_nonneg.2 h0
    rw [hd] at this
    exact nonneg_of_mul_nonneg_right this hpos
  have h2 : ((n₂ - n₁ : ℤ) : ℝ) < 1 := by
    rw [hd] at hlt
    nlinarith
  have h3 : n₂ - n₁ = 0 := by
    have a1 : 0 ≤ n₂ - n₁ := by exact_mod_cast h1
    have a2 : n₂ - n₁ < 1 := by exact_mod_cast h2
    omega
  have : K.left - J.right = 0 := by rw [hd, h3]; simp
  linarith

/-- **The gap lemma**: two Whitney intervals `J` (left) and `K` (right) with a gap smaller than
`1/50` of the length of one of them are adjacent: `K.left = J.right`. -/
theorem IsWhitney.left_eq_right_of_gap (hJ : J.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ')
    (h : J.right ≤ K.left)
    (hg : K.left - J.right < J.length / 50 ∨ K.left - J.right < K.length / 50) :
    K.left = J.right := by
  obtain ⟨c1, c2⟩ := hJ.comparable hK h
  have hg0 : 0 ≤ K.left - J.right := sub_nonneg.2 h
  have hL := J.length_pos
  have hLK := K.length_pos
  apply left_eq_right_of_lt h
  · rcases hg with hg | hg <;> linarith
  · rcases hg with hg | hg <;> linarith

/-! ### Neighbours -/

/-- Every Whitney interval has a Whitney right neighbour: `K.left = J.right`. -/
theorem IsWhitney.exists_right_nbr (hJ : J.IsWhitney ξ ξ') :
    ∃ K : Dyadic, K.IsWhitney ξ ξ' ∧ K.left = J.right := by
  have hL := J.length_pos
  have hJr := J.right_eq
  have hmem : J.right ∈ Ioo ξ ξ' := ⟨by linarith [hJ.1.1], by linarith [hJ.1.2]⟩
  obtain ⟨K, hK, hKm⟩ := exists_isWhitney_mem hmem
  refine ⟨K, hK, ?_⟩
  by_contra hne
  have hlt : K.left < J.right := lt_of_le_of_ne hKm.1 hne
  have hz1 : max K.left J.left ∈ K.toSet :=
    ⟨le_max_left _ _, max_lt K.left_lt_right (lt_trans J.left_lt_right hKm.2)⟩
  have hz2 : max K.left J.left ∈ J.toSet :=
    ⟨le_max_right _ _, max_lt hlt (by linarith)⟩
  rcases hJ.eq_or_disjoint hK with h | h
  · subst h
    exact lt_irrefl _ hKm.2
  · exact Set.disjoint_left.1 h hz2 hz1

/-- Every Whitney interval has a Whitney left neighbour: `K.right = J.left`. -/
theorem IsWhitney.exists_left_nbr (hJ : J.IsWhitney ξ ξ') :
    ∃ K : Dyadic, K.IsWhitney ξ ξ' ∧ K.right = J.left := by
  have hL := J.length_pos
  have hJr := J.right_eq
  have hz : J.left - J.length / 100 ∈ Ioo ξ ξ' :=
    ⟨by linarith [hJ.1.1], by linarith [hJ.1.2]⟩
  obtain ⟨K, hK, hKz⟩ := exists_isWhitney_mem hz
  have h1 : K.right ≤ J.left := by
    by_contra hlt
    rw [not_le] at hlt
    have hmemK : J.left ∈ K.toSet := ⟨by linarith [hKz.1], hlt⟩
    rcases hK.eq_or_disjoint hJ with h | h
    · subst h
      linarith [hKz.1, hKz.2]
    · exact Set.disjoint_left.1 h hmemK J.left_mem_toSet
  refine ⟨K, hK, ?_⟩
  have := hK.left_eq_right_of_gap hJ h1 (Or.inr (by linarith [hKz.2]))
  exact this.symm

/-- The left neighbour of a Whitney interval is unique. -/
theorem IsWhitney.eq_of_right_eq (hJ : J.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ')
    (h : J.right = K.right) : J = K := by
  rcases hJ.eq_or_disjoint hK with h' | hd
  · exact h'
  · exfalso
    have hJr := J.right_eq
    have hKr := K.right_eq
    have hm : 0 < min J.length K.length := lt_min J.length_pos K.length_pos
    have h1 := min_le_left J.length K.length
    have h2 := min_le_right J.length K.length
    have hz1 : J.right - min J.length K.length / 2 ∈ J.toSet := ⟨by linarith, by linarith⟩
    have hz2 : J.right - min J.length K.length / 2 ∈ K.toSet := ⟨by linarith, by linarith⟩
    exact Set.disjoint_left.1 hd hz1 hz2

/-- The right neighbour of a Whitney interval is unique. -/
theorem IsWhitney.eq_of_left_eq (hJ : J.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ')
    (h : J.left = K.left) : J = K := by
  rcases hJ.eq_or_disjoint hK with h' | hd
  · exact h'
  · exfalso
    have hJr := J.right_eq
    have hKr := K.right_eq
    have hm : 0 < min J.length K.length := lt_min J.length_pos K.length_pos
    have h1 := min_le_left J.length K.length
    have h2 := min_le_right J.length K.length
    have hz1 : J.left + min J.length K.length / 2 ∈ J.toSet := ⟨by linarith, by linarith⟩
    have hz2 : J.left + min J.length K.length / 2 ∈ K.toSet := ⟨by linarith, by linarith⟩
    exact Set.disjoint_left.1 hd hz1 hz2

/-- Disjoint dyadic intervals are ordered: one lies to the left of the other. -/
theorem right_le_left_of_disjoint (h : Disjoint J.toSet K.toSet) :
    J.right ≤ K.left ∨ K.right ≤ J.left := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  have hz1 : max J.left K.left ∈ J.toSet :=
    ⟨le_max_left _ _, max_lt J.left_lt_right hcon.1⟩
  have hz2 : max J.left K.left ∈ K.toSet :=
    ⟨le_max_right _ _, max_lt hcon.2 K.left_lt_right⟩
  exact Set.disjoint_left.1 h hz1 hz2

/-- Adjacent Whitney intervals have comparable lengths. -/
theorem IsWhitney.nbr_length_lt (hJ : J.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ')
    (h : K.right = J.left) : K.length < 4 * J.length ∧ J.length < 4 * K.length := by
  have := hK.comparable hJ h.le
  rw [← h, sub_self, sub_zero, sub_zero] at this
  exact ⟨this.1, this.2⟩

/-- Adjacent Whitney intervals have scales differing by at most `1`
(`|J'| ∈ {|J|/2, |J|, 2|J|}`, [O+] L961-L964). -/
theorem IsWhitney.nbr_k (hJ : J.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ')
    (h : K.right = J.left) : J.k - 1 ≤ K.k ∧ K.k ≤ J.k + 1 := by
  obtain ⟨h1, h2⟩ := hJ.nbr_length_lt hK h
  have e : ∀ n : ℤ, (4 : ℝ) * 2 ^ n = 2 ^ (n + 2) := fun n => by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  have a1 : (2 : ℝ) ^ K.k < 2 ^ (J.k + 2) := by
    have : K.length = 2 ^ K.k := rfl
    have h' : J.length = 2 ^ J.k := rfl
    rw [← e, ← this]; rw [h'] at h1; linarith [h1]
  have a2 : (2 : ℝ) ^ J.k < 2 ^ (K.k + 2) := by
    have : K.length = 2 ^ K.k := rfl
    have h' : J.length = 2 ^ J.k := rfl
    rw [← e, ← this]; rw [h'] at h2; linarith [h2]
  have b1 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 a1
  have b2 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 a2
  omega

/-- Adjacent Whitney intervals: `|J'| ≤ 2|J|` and `|J| ≤ 2|J'|`. -/
theorem IsWhitney.nbr_length_le (hJ : J.IsWhitney ξ ξ') (hK : K.IsWhitney ξ ξ')
    (h : K.right = J.left) : K.length ≤ 2 * J.length ∧ J.length ≤ 2 * K.length := by
  obtain ⟨h1, h2⟩ := hJ.nbr_k hK h
  have e : ∀ n : ℤ, (2 : ℝ) * 2 ^ n = 2 ^ (n + 1) := fun n => by
    rw [zpow_add_one₀ (by norm_num)]; ring
  constructor
  · have : (2 : ℝ) ^ K.k ≤ 2 ^ (J.k + 1) := zpow_le_zpow_right₀ (by norm_num) h2
    rw [← e] at this
    exact this
  · have : (2 : ℝ) ^ J.k ≤ 2 ^ (K.k + 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [← e] at this
    exact this

open Classical in
/-- The exponent `i(J)` of [O+] L961-L964: `|J'| = 2^{i(J)} |J|` for the left Whitney neighbour
`J'` of `J` (`0` if `J` has none, which cannot happen for a Whitney interval). -/
def nbrIdx (ξ ξ' : ℝ) (J : Dyadic) : ℤ :=
  if h : ∃ K : Dyadic, K.IsWhitney ξ ξ' ∧ K.right = J.left then h.choose.k - J.k else 0

/-- `i(J) = k_{J'} - k_J` for the left Whitney neighbour `J'`. -/
theorem nbrIdx_eq (hK : K.IsWhitney ξ ξ') (h : K.right = J.left) :
    nbrIdx ξ ξ' J = K.k - J.k := by
  have hex : ∃ K : Dyadic, K.IsWhitney ξ ξ' ∧ K.right = J.left := ⟨K, hK, h⟩
  simp only [nbrIdx, hex, ↓reduceDIte]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have := h1.eq_of_right_eq hK (h2.trans h.symm)
  rw [this]

/-- `i(J) ∈ {-1, 0, 1}` ([O+] L961-L964). -/
theorem nbrIdx_mem (hJ : J.IsWhitney ξ ξ') : -1 ≤ nbrIdx ξ ξ' J ∧ nbrIdx ξ ξ' J ≤ 1 := by
  obtain ⟨K, hK, h⟩ := hJ.exists_left_nbr
  rw [nbrIdx_eq hK h]
  have := hJ.nbr_k hK h
  omega

/-- The left Whitney neighbour `J'` of a Whitney interval `J` exists, is unique, ends where `J`
begins and has length `2^{i(J)} |J|`. -/
theorem IsWhitney.exists_left_nbr_length (hJ : J.IsWhitney ξ ξ') :
    ∃ K : Dyadic, K.IsWhitney ξ ξ' ∧ K.right = J.left ∧
      K.length = 2 ^ nbrIdx ξ ξ' J * J.length := by
  obtain ⟨K, hK, h⟩ := hJ.exists_left_nbr
  refine ⟨K, hK, h, ?_⟩
  rw [nbrIdx_eq hK h]
  unfold length
  rw [← zpow_add₀ (by norm_num)]
  congr 1; ring

/-! ### Geometry of parents, children and translates -/

/-- `J ⊆ (ξ, ξ')` iff `ξ < a` and `b ≤ ξ'`. -/
theorem toSet_subset_Ioo_iff : J.toSet ⊆ Ioo ξ ξ' ↔ ξ < J.left ∧ J.right ≤ ξ' := by
  constructor
  · intro h
    refine ⟨(h J.left_mem_toSet).1, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hm : max ξ' J.left < J.right := max_lt hlt J.left_lt_right
    have hx : (max ξ' J.left + J.right) / 2 ∈ J.toSet :=
      ⟨by linarith [le_max_right ξ' J.left], by linarith⟩
    have := (h hx).2
    linarith [le_max_left ξ' J.left]
  · rintro ⟨h1, h2⟩ x ⟨hx1, hx2⟩
    exact ⟨by linarith, by linarith⟩

theorem side_eq_left_iff : J.side = Side.left ↔ J.m % 2 = 0 := by
  unfold side
  split_ifs with h <;> simp [h]

theorem side_eq_right_iff : J.side = Side.right ↔ J.m % 2 = 1 := by
  unfold side
  split_ifs with h
  · simp [h]
  · simp; omega

/-- The parent of a left child begins where the child does. -/
theorem parent_left_of_side_left (h : J.side = Side.left) : J.parent.left = J.left := by
  have h2 : J.m % 2 = 0 := side_eq_left_iff.1 h
  have h3 : J.m = 2 * (J.m / 2) := by omega
  have h4 : (J.m : ℝ) = 2 * ((J.m / 2 : ℤ) : ℝ) := by exact_mod_cast h3
  unfold left parent
  simp only
  rw [zpow_add_one₀ (by norm_num), h4]
  ring

/-- The parent of a right child begins one length earlier. -/
theorem parent_left_of_side_right (h : J.side = Side.right) :
    J.parent.left = J.left - J.length := by
  have h2 : J.m % 2 = 1 := side_eq_right_iff.1 h
  have h3 : J.m = 2 * (J.m / 2) + 1 := by omega
  have h4 : (J.m : ℝ) = 2 * ((J.m / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast h3
  unfold left parent length
  simp only
  rw [zpow_add_one₀ (by norm_num), h4]
  ring

/-- The parent of a left child ends one length later. -/
theorem parent_right_of_side_left (h : J.side = Side.left) :
    J.parent.right = J.right + J.length := by
  rw [parent_right_eq, parent_left_of_side_left h, length_parent, right_eq]; ring
where
  parent_right_eq : J.parent.right = J.parent.left + J.parent.length := J.parent.right_eq

/-- The parent of a right child ends where the child does. -/
theorem parent_right_of_side_right (h : J.side = Side.right) : J.parent.right = J.right := by
  rw [J.parent.right_eq, parent_left_of_side_right h, length_parent, right_eq]; ring

/-- Translation by `-1` swaps the side. -/
theorem side_shift_neg_one : (J.shift (-1)).side = J.side.opp := by
  unfold side shift Side.opp
  split_ifs with h1 h2 h2 <;> simp_all <;> omega

/-- The left end point of a child. -/
theorem left_child (s : Side) : (J.child s).left = J.left + s.offset * (J.length / 2) := by
  unfold left child length
  simp only
  rw [zpow_sub_one₀ (by norm_num)]
  push_cast
  ring

/-- The right end point of a child. -/
theorem right_child (s : Side) : (J.child s).right = J.left + (s.offset + 1) * (J.length / 2) := by
  rw [right_eq, left_child, length_child]; ring

/-- If `ξ` avoids the dyadic end points then `a - ξ` is not an integer multiple of `|J|`. -/
theorem left_sub_ne_int_mul (hξ : ∀ n m : ℤ, ξ ≠ n * 2 ^ m) (n : ℤ) :
    J.left - ξ ≠ n * J.length := by
  intro h
  refine hξ (J.m - n) J.k ?_
  unfold left length at h
  push_cast
  linarith

/-- **Whitney intervals in terms of `A = a - ξ`, `B = ξ' - b`, `ℓ = |J|`** (and the side of `J`). -/
theorem isWhitney_iff_AB : J.IsWhitney ξ ξ' ↔ J.length ≤ J.left - ξ ∧ J.length ≤ ξ' - J.right ∧
    (J.side = Side.left → J.left - ξ < 2 * J.length ∨ ξ' - J.right < 3 * J.length) ∧
    (J.side = Side.right → J.left - ξ < 3 * J.length ∨ ξ' - J.right < 2 * J.length) := by
  rw [isWhitney_iff]
  unfold Admissible
  have hr := J.right_eq
  have hp := J.length_parent
  constructor
  · rintro ⟨⟨h1, h2⟩, hP⟩
    refine ⟨by linarith, by linarith, fun hs => ?_, fun hs => ?_⟩
    · rw [not_and_or, not_le, not_le, parent_left_of_side_left hs, parent_right_of_side_left hs,
        hp] at hP
      rcases hP with h | h
      · left; linarith
      · right; linarith
    · rw [not_and_or, not_le, not_le, parent_left_of_side_right hs, parent_right_of_side_right hs,
        hp] at hP
      rcases hP with h | h
      · left; linarith
      · right; linarith
  · rintro ⟨h1, h2, hL, hR⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rintro ⟨h3, h4⟩
    cases hs : J.side
    · rcases hL hs with h | h
      · rw [parent_left_of_side_left hs, hp] at h3; linarith
      · rw [parent_right_of_side_left hs, hp] at h4; linarith
    · rcases hR hs with h | h
      · rw [parent_left_of_side_right hs, hp] at h3; linarith
      · rw [parent_right_of_side_right hs, hp] at h4; linarith

end Dyadic

/-! ### The ten classes in terms of `A = a - ξ`, `B = ξ' - b`, `ℓ = |J|` -/

/-- The position conditions of the class `ρ ∈ R` in terms of `ℓ = |J|`, `A = a - ξ` and
`B = ξ' - b` (`J = [a, b)`): `ξ ∈ J - (m+1)|J|` reads `mℓ < A ≤ (m+1)ℓ`, `ξ' ∈ J + (n+1)|J|` reads
`nℓ ≤ B < (n+1)ℓ`, `dis(ξ', J) ≥ nℓ` reads `nℓ ≤ B` and `dis(ξ, J) > mℓ` reads `mℓ < A`. -/
def RIdx.pos : RIdx → ℝ → ℝ → ℝ → Prop
  | .r121L, ℓ, A, B => 2 * ℓ < A ∧ A ≤ 3 * ℓ ∧ ℓ ≤ B ∧ B < 2 * ℓ
  | .r122L, ℓ, A, B => 2 * ℓ < A ∧ A ≤ 3 * ℓ ∧ 2 * ℓ ≤ B ∧ B < 3 * ℓ
  | .r131L, ℓ, A, B => 3 * ℓ < A ∧ A ≤ 4 * ℓ ∧ ℓ ≤ B ∧ B < 2 * ℓ
  | .r132L, ℓ, A, B => 3 * ℓ < A ∧ A ≤ 4 * ℓ ∧ 2 * ℓ ≤ B ∧ B < 3 * ℓ
  | .r211L, ℓ, A, B => ℓ < A ∧ A ≤ 2 * ℓ ∧ ℓ ≤ B
  | .r211R, ℓ, A, B => ℓ < A ∧ A ≤ 2 * ℓ ∧ ℓ ≤ B
  | .r221R, ℓ, A, B => 2 * ℓ < A ∧ A ≤ 3 * ℓ ∧ ℓ ≤ B
  | .r341L, ℓ, A, B => 4 * ℓ < A ∧ ℓ ≤ B ∧ B < 2 * ℓ
  | .r331R, ℓ, A, B => 3 * ℓ < A ∧ ℓ ≤ B ∧ B < 2 * ℓ
  | .r342L, ℓ, A, B => 4 * ℓ < A ∧ 2 * ℓ ≤ B ∧ B < 3 * ℓ

/-- `J ∈ 𝒥_{ξ,ξ',ρ}` iff `J` has the side of `ρ` and the position conditions `ρ.pos`. -/
theorem inClass_iff (ρ : RIdx) (ξ ξ' : ℝ) (J : Dyadic) :
    InClass ρ.toIdx ξ ξ' J ↔ J.side = ρ.toIdx.side ∧
      ρ.pos J.length (J.left - ξ) (ξ' - J.right) := by
  have hL := J.length_pos
  have hr := J.right_eq
  have hsub := @Dyadic.toSet_subset_Ioo_iff ξ ξ' J
  unfold InClass
  rw [hsub]
  cases ρ <;>
  simp only [RIdx.toIdx, RIdx.pos, Idx.ωl, Idx.ωh, Idx.ωlDyadic,
    Dyadic.toSet, Dyadic.left_shift, Dyadic.right_shift, Set.mem_Ico, Set.mem_Iio, Set.mem_Ici] <;>
  push_cast <;>
  first
    | (constructor
       · rintro ⟨⟨x1, x2⟩, hs, ⟨c1, c2⟩, c3, c4⟩
         exact ⟨hs, by linarith, by linarith, by linarith, by linarith⟩
       · rintro ⟨hs, p1, p2, p3, p4⟩
         exact ⟨⟨by linarith, by linarith⟩, hs, ⟨by linarith, by linarith⟩, by linarith,
           by linarith⟩)
    | (constructor
       · rintro ⟨⟨x1, x2⟩, hs, ⟨c1, c2⟩, c3⟩
         exact ⟨hs, by linarith, by linarith, by linarith⟩
       · rintro ⟨hs, p1, p2, p3⟩
         exact ⟨⟨by linarith, by linarith⟩, hs, ⟨by linarith, by linarith⟩, by linarith⟩)
    | (constructor
       · rintro ⟨⟨x1, x2⟩, hs, c1, c3, c4⟩
         exact ⟨hs, by linarith, by linarith, by linarith⟩
       · rintro ⟨hs, p1, p2, p3⟩
         exact ⟨⟨by linarith, by linarith⟩, hs, by linarith, by linarith, by linarith⟩)

namespace Dyadic

/-- **Every Whitney interval lies in one of the ten classes** (when `ξ, ξ'` avoid the dyadic end
points): `𝒥_{ξ,ξ'} ⊆ ⋃_{ρ ∈ R} 𝒥_{ξ,ξ',ρ}` ([O+] L1054-L1057). -/
theorem IsWhitney.exists_inClass {ξ ξ' : ℝ} {J : Dyadic} (hξ : ∀ n m : ℤ, ξ ≠ n * 2 ^ m)
    (hJ : J.IsWhitney ξ ξ') : ∃ ρ : RIdx, InClass ρ.toIdx ξ ξ' J := by
  obtain ⟨hA, hB, hL, hR⟩ := isWhitney_iff_AB.1 hJ
  have n2 : J.left - ξ ≠ 2 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 2
  have n3 : J.left - ξ ≠ 3 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 3
  have n4 : J.left - ξ ≠ 4 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 4
  have n1 : J.left - ξ ≠ 1 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 1
  have hℓ := J.length_pos
  have hA1 : J.length < J.left - ξ := lt_of_le_of_ne hA (by simpa using n1.symm)
  cases hs : J.side
  · -- left child
    have hL' := hL hs
    by_cases h2 : J.left - ξ < 2 * J.length
    · exact ⟨.r211L, (inClass_iff _ _ _ _).2 ⟨hs, by
        simp only [RIdx.pos]; refine ⟨?_, ?_, ?_⟩ <;> linarith⟩⟩
    · have hA2 : 2 * J.length < J.left - ξ := lt_of_le_of_ne (not_lt.1 h2) n2.symm
      have hB3 : ξ' - J.right < 3 * J.length := by
        rcases hL' with h | h
        · exact absurd h h2
        · exact h
      by_cases h3 : J.left - ξ < 3 * J.length
      · by_cases hb : ξ' - J.right < 2 * J.length
        · exact ⟨.r121L, (inClass_iff _ _ _ _).2 ⟨hs, by
            simp only [RIdx.pos]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith⟩⟩
        · exact ⟨.r122L, (inClass_iff _ _ _ _).2 ⟨hs, by
            simp only [RIdx.pos]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [not_lt.1 hb]⟩⟩
      · have hA3 : 3 * J.length < J.left - ξ := lt_of_le_of_ne (not_lt.1 h3) n3.symm
        by_cases h4 : J.left - ξ < 4 * J.length
        · by_cases hb : ξ' - J.right < 2 * J.length
          · exact ⟨.r131L, (inClass_iff _ _ _ _).2 ⟨hs, by
              simp only [RIdx.pos]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith⟩⟩
          · exact ⟨.r132L, (inClass_iff _ _ _ _).2 ⟨hs, by
              simp only [RIdx.pos]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [not_lt.1 hb]⟩⟩
        · have hA4 : 4 * J.length < J.left - ξ := lt_of_le_of_ne (not_lt.1 h4) n4.symm
          by_cases hb : ξ' - J.right < 2 * J.length
          · exact ⟨.r341L, (inClass_iff _ _ _ _).2 ⟨hs, by
              simp only [RIdx.pos]; refine ⟨?_, ?_, ?_⟩ <;> linarith⟩⟩
          · exact ⟨.r342L, (inClass_iff _ _ _ _).2 ⟨hs, by
              simp only [RIdx.pos]; refine ⟨?_, ?_, ?_⟩ <;> linarith [not_lt.1 hb]⟩⟩
  · -- right child
    have hR' := hR hs
    by_cases h2 : J.left - ξ < 2 * J.length
    · exact ⟨.r211R, (inClass_iff _ _ _ _).2 ⟨hs, by
        simp only [RIdx.pos]; refine ⟨?_, ?_, ?_⟩ <;> linarith⟩⟩
    · have hA2 : 2 * J.length < J.left - ξ := lt_of_le_of_ne (not_lt.1 h2) n2.symm
      by_cases h3 : J.left - ξ < 3 * J.length
      · exact ⟨.r221R, (inClass_iff _ _ _ _).2 ⟨hs, by
          simp only [RIdx.pos]; refine ⟨?_, ?_, ?_⟩ <;> linarith⟩⟩
      · have hA3 : 3 * J.length < J.left - ξ := lt_of_le_of_ne (not_lt.1 h3) n3.symm
        have hB2 : ξ' - J.right < 2 * J.length := by
          rcases hR' with h | h
          · exact absurd h h3
          · exact h
        exact ⟨.r331R, (inClass_iff _ _ _ _).2 ⟨hs, by
          simp only [RIdx.pos]; refine ⟨?_, ?_, ?_⟩ <;> linarith⟩⟩

/-- **Conversely, every class is contained in `𝒥_{ξ,ξ'}`** (when `ξ` avoids the dyadic end
points): the position conditions of a class `ρ ∈ R` force `J` to be a maximal admissible
interval ([O+] L1054-L1057). -/
theorem isWhitney_of_inClass {ξ ξ' : ℝ} {J : Dyadic} (hξ : ∀ n m : ℤ, ξ ≠ n * 2 ^ m)
    (ρ : RIdx) (h : InClass ρ.toIdx ξ ξ' J) : J.IsWhitney ξ ξ' := by
  obtain ⟨hs, hp⟩ := (inClass_iff _ _ _ _).1 h
  have n2 : J.left - ξ ≠ 2 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 2
  have n3 : J.left - ξ ≠ 3 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 3
  have hℓ := J.length_pos
  rw [isWhitney_iff_AB]
  cases ρ <;> simp only [RIdx.pos, RIdx.toIdx] at hp hs <;> rw [hs]
  · obtain ⟨a1, a2, a3, a4⟩ := hp
    refine ⟨by linarith, by linarith, fun _ => Or.inr (by linarith), fun h => by simp at h⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hp
    refine ⟨by linarith, by linarith, fun _ => Or.inr (by linarith), fun h => by simp at h⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hp
    refine ⟨by linarith, by linarith, fun _ => Or.inr (by linarith), fun h => by simp at h⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hp
    refine ⟨by linarith, by linarith, fun _ => Or.inr (by linarith), fun h => by simp at h⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    refine ⟨by linarith, by linarith, fun _ => Or.inl (lt_of_le_of_ne a2 n2), fun h => by simp at h⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    refine ⟨by linarith, by linarith, fun h => by simp at h, fun _ => Or.inl (by linarith)⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    refine ⟨by linarith, by linarith, fun h => by simp at h, fun _ => Or.inl (lt_of_le_of_ne a2 n3)⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    refine ⟨by linarith, by linarith, fun _ => Or.inr (by linarith), fun h => by simp at h⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    refine ⟨by linarith, by linarith, fun h => by simp at h, fun _ => Or.inr (by linarith)⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    refine ⟨by linarith, by linarith, fun _ => Or.inr (by linarith), fun h => by simp at h⟩

/-! ### The left neighbour of a class interval -/

section Nbr

variable {ξ ξ' : ℝ} {J : Dyadic}

/-- Shape `i = 0`: the translate `J - |J|` (for a left child). -/
theorem isWhitney_shift_neg_one_of_left (hs : J.side = Side.left)
    (h1 : 2 * J.length ≤ J.left - ξ) (hB : J.length ≤ ξ' - J.right)
    (h3 : J.left - ξ < 4 * J.length) : (J.shift (-1)).IsWhitney ξ ξ' := by
  have hr := J.right_eq
  have hℓ := J.length_pos
  rw [isWhitney_iff_AB]
  simp only [length_shift, left_shift, right_shift, side_shift_neg_one, hs, Side.opp]
  push_cast
  refine ⟨by linarith, by linarith, fun h => by simp at h, fun _ => Or.inl (by linarith)⟩

/-- Shape `i = 0`: the translate `J - |J|` (for a right child). -/
theorem isWhitney_shift_neg_one_of_right (hs : J.side = Side.right)
    (h1 : 2 * J.length ≤ J.left - ξ) (hB : J.length ≤ ξ' - J.right)
    (h3 : J.left - ξ < 3 * J.length ∨ ξ' - J.right < 2 * J.length) :
    (J.shift (-1)).IsWhitney ξ ξ' := by
  have hr := J.right_eq
  have hℓ := J.length_pos
  rw [isWhitney_iff_AB]
  simp only [length_shift, left_shift, right_shift, side_shift_neg_one, hs, Side.opp]
  push_cast
  refine ⟨by linarith, by linarith, fun _ => ?_, fun h => by simp at h⟩
  rcases h3 with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Shape `i = -1`: the right half of the translate `J - |J|`. -/
theorem isWhitney_child_shift (hA : J.length ≤ J.left - ξ) (hA2 : J.left - ξ < 2 * J.length)
    (hB : 0 ≤ ξ' - J.right) : ((J.shift (-1)).child Side.right).IsWhitney ξ ξ' := by
  have hr := J.right_eq
  have hℓ := J.length_pos
  rw [isWhitney_iff_AB]
  simp only [length_child, side_child, left_child, right_child, length_shift, left_shift,
    Side.offset]
  push_cast
  refine ⟨by linarith, by linarith, fun h => by simp at h, fun _ => Or.inl (by linarith)⟩

/-- Shape `i = 1`: the translate `J.parent - |J.parent|` (for a left child). -/
theorem isWhitney_parent_shift (hs : J.side = Side.left) (hA : 4 * J.length ≤ J.left - ξ)
    (hB1 : J.length ≤ ξ' - J.right) (hB2 : ξ' - J.right < 3 * J.length) :
    (J.parent.shift (-1)).IsWhitney ξ ξ' := by
  have hr := J.right_eq
  have hℓ := J.length_pos
  have hp := J.length_parent
  have hpl := parent_left_of_side_left hs
  have hpr := parent_right_of_side_left hs
  have hpr2 := J.parent.right_eq
  rw [isWhitney_iff_AB]
  simp only [length_shift, left_shift, right_shift]
  push_cast
  refine ⟨by linarith, by linarith, fun _ => Or.inr (by linarith), fun _ => Or.inr (by linarith)⟩

/-- **The left Whitney neighbour of a class-`ρ` interval** ([O+] L1054-L1057):
there is a Whitney interval `K` ending where `J` begins, of scale `k_J + i(ρ)`, i.e. of length
`2^{i(ρ)} |J|`. -/
theorem exists_nbr_of_inClass (hξ : ∀ n m : ℤ, ξ ≠ n * 2 ^ m) (ρ : RIdx)
    (h : InClass ρ.toIdx ξ ξ' J) :
    ∃ K : Dyadic, K.IsWhitney ξ ξ' ∧ K.right = J.left ∧ K.k = J.k + ρ.i := by
  obtain ⟨hs, hp⟩ := (inClass_iff _ _ _ _).1 h
  have n2 : J.left - ξ ≠ 2 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 2
  have n3 : J.left - ξ ≠ 3 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 3
  have n4 : J.left - ξ ≠ 4 * J.length := by simpa using left_sub_ne_int_mul (J := J) hξ 4
  have hr := J.right_eq
  have hℓ := J.length_pos
  have hs' : J.side = _ := hs
  simp only [RIdx.pos, RIdx.toIdx] at hp hs
  have hk0 : (J.shift (-1)).right = J.left := by rw [right_shift]; push_cast; linarith
  have hk1 : ((J.shift (-1)).child Side.right).right = J.left := by
    rw [right_child, left_shift, length_shift]; push_cast; simp [Side.offset]; linarith
  cases ρ
  · obtain ⟨a1, a2, a3, a4⟩ := hp
    exact ⟨J.shift (-1), isWhitney_shift_neg_one_of_left hs (by linarith) (by linarith)
      (by linarith), hk0, by simp [RIdx.i]⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hp
    exact ⟨J.shift (-1), isWhitney_shift_neg_one_of_left hs (by linarith) (by linarith)
      (by linarith), hk0, by simp [RIdx.i]⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hp
    exact ⟨J.shift (-1), isWhitney_shift_neg_one_of_left hs (by linarith) (by linarith)
      (lt_of_le_of_ne a2 n4), hk0, by simp [RIdx.i]⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hp
    exact ⟨J.shift (-1), isWhitney_shift_neg_one_of_left hs (by linarith) (by linarith)
      (lt_of_le_of_ne a2 n4), hk0, by simp [RIdx.i]⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    exact ⟨(J.shift (-1)).child Side.right,
      isWhitney_child_shift (by linarith) (lt_of_le_of_ne a2 n2) (by linarith), hk1,
      by simp [RIdx.i, child]; ring⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    exact ⟨(J.shift (-1)).child Side.right,
      isWhitney_child_shift (by linarith) (lt_of_le_of_ne a2 n2) (by linarith), hk1,
      by simp [RIdx.i, child]; ring⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    exact ⟨J.shift (-1), isWhitney_shift_neg_one_of_right hs (by linarith) (by linarith)
      (Or.inl (lt_of_le_of_ne a2 n3)), hk0, by simp [RIdx.i]⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    have hpr := parent_right_of_side_left hs
    refine ⟨J.parent.shift (-1), isWhitney_parent_shift hs (by linarith) (by linarith)
      (by linarith), ?_, by simp [RIdx.i]⟩
    rw [right_shift, hpr, length_parent]; push_cast; linarith
  · obtain ⟨a1, a2, a3⟩ := hp
    exact ⟨J.shift (-1), isWhitney_shift_neg_one_of_right hs (by linarith) (by linarith)
      (Or.inr a3), hk0, by simp [RIdx.i]⟩
  · obtain ⟨a1, a2, a3⟩ := hp
    have hpr := parent_right_of_side_left hs
    refine ⟨J.parent.shift (-1), isWhitney_parent_shift hs (by linarith) (by linarith)
      (by linarith), ?_, by simp [RIdx.i]⟩
    rw [right_shift, hpr, length_parent]; push_cast; linarith

end Nbr

/-- **`i(J) = i(ρ)`**: the exponent of the left Whitney neighbour of a class-`ρ` interval is the
number `i(ρ) ∈ {-1, 0, 1}` of `R` ([O+] L1054-L1057). -/
theorem nbrIdx_of_inClass {ξ ξ' : ℝ} {J : Dyadic} (hξ : ∀ n m : ℤ, ξ ≠ n * 2 ^ m) (ρ : RIdx)
    (h : InClass ρ.toIdx ξ ξ' J) : nbrIdx ξ ξ' J = ρ.i := by
  obtain ⟨K, hK, hKr, hk⟩ := exists_nbr_of_inClass hξ ρ h
  rw [nbrIdx_eq hK hKr, hk]
  ring

/-- **Each Whitney interval lies in exactly one class** ([O+] L1054-L1057). -/
theorem IsWhitney.existsUnique_inClass {ξ ξ' : ℝ} {J : Dyadic} (hξ : ∀ n m : ℤ, ξ ≠ n * 2 ^ m)
    (hJ : J.IsWhitney ξ ξ') : ∃! ρ : RIdx, InClass ρ.toIdx ξ ξ' J := by
  obtain ⟨ρ, hρ⟩ := hJ.exists_inClass hξ
  exact ⟨ρ, hρ, fun ρ' hρ' => by
    by_contra hne
    exact inClass_disjoint (Ne.symm hne) ξ ξ' J ⟨hρ, hρ'⟩⟩

end Dyadic

end PrimeCarleson.Proof.Oplus
