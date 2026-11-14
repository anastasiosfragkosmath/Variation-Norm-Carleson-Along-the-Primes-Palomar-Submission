module

public import PrimeCarleson.Proof.Oplus.Defs.Dyadic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# The multitile indices `(i, m, n, side)` and the index set `R` ([O+] L1040-L1057)

Source: [O+], L1040–L1057 and, for the sets `ω_l, ω_h`, L1069-L1082: the wave packets are sorted
by the position of the frequencies `ξ < ξ'` relative to the dyadic interval `J`, into the classes
`𝒥_{ξ,ξ',ρ}` indexed by `ρ = (i, m, n, side) ∈ {1,2,3} × {1,2,3,4}² × {left, right}`, and
`R` is "an explicit subset" of ten indices, chosen so that the classes `𝒥_{ξ,ξ',ρ}`, `ρ ∈ R`,
partition `𝒥_{ξ,ξ'}` and the left neighbour has size `2^{i(ρ)}|J|`.

* `Idx` is the index `(typ, m, n, side)` for *any* values; `Idx.IsStd` says `m, n ∈ {1, …, 4}`.
  Nothing downstream is tied to membership in `R` (the reflection of L1113-L1118 produces
  indices outside `R`).
* `Idx.ωl ρ u`, `Idx.ωh ρ u`: the frequency sets `ω_l, ω_h` of the `ρ`-multitile with
  `ω_u = u` (L1074-L1082); `Idx.ωlDyadic ρ u = u - (m+1)|u|` (the finite interval that is `ω_l`
  for the 1- and 2-indices).
* `InClass ρ ξ ξ' J` is `J ∈ 𝒥_{ξ,ξ',ρ}` (L1046-L1051), expressed through `ω_l, ω_h`
  (`inClass_iff`): `J ⊂ (ξ, ξ')`, `J` the `side`-child of its parent, `ξ ∈ ω_l(J)`, `ξ' ∈ ω_h(J)`.
  (For `i = 2` the printed `dis(ξ', J) ≥ n|J|` is `ξ' ≥ b + n|J| = a + (n+1)|J|`, and for `i = 3`
  the printed `dis(ξ, J) > m|J|` is `ξ < a - m|J| = b - (m+1)|J|`, because `J ⊂ (ξ, ξ')`.)
* `R : Finset Idx` is the printed set of ten indices; `RIdx` is the same set as a ten-element
  enumeration, on which the size ratio `i(ρ) ∈ {-1, 0, 1}` is a total function (`RIdx.i`). The
  values of `i` are not printed in [O+]; they are computed from the Whitney geometry (the left
  neighbour of `J ∈ 𝒥_{ξ,ξ',ρ}` has size `2^{i(ρ)}|J|`); the statement that they equal the
  neighbour ratios is part of
  the claims of L1040-L1057 and L961-L964 of [O+] and is proved with the Whitney intervals, not
  here.
* finite facts proved here: `RIdx.i_mem`, `RIdx.toIdx_isStd` (the ten indices are standard, with
  `m, n ∈ {1, …, 4}`), and `inClass_disjoint`: the ten classes are pairwise disjoint for every
  `ξ, ξ', J`.

NOTE (on [O+], L1040–L1057): the partition `𝒥_{ξ,ξ'} = ⋃_{ρ ∈ R} 𝒥_{ξ,ξ',ρ}`
fails at dyadic end points, for instance for `ξ = a - |J|` and `J = [a, b)`, which lies in no class
(types 1 and 2 need `ξ ∈ [a - (m+1)|J|, a - m|J|)` with `m ≥ 1`, type 3 needs
`dis(ξ, J) > m|J|`); it holds when `ξ, ξ'` are not of the form `n 2^k`, the standing assumption
on `Ξ` at L897-L899.
-/

@[expose] public noncomputable section

open Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The type `i ∈ {1, 2, 3}` of an index `ρ = (i, m, n, side)` (L1073-L1082). -/
inductive IdxType where
  | one
  | two
  | three
  deriving DecidableEq

/-- An index `ρ = (i, m, n, side)` (L1040-L1051), for arbitrary values of `m, n`. -/
structure Idx where
  /-- The type `i ∈ {1, 2, 3}`. -/
  typ : IdxType
  /-- The parameter `m` (`ξ ∈ J - (m+1)|J|`, or `dis(ξ, J) > m|J|`). -/
  m : ℕ
  /-- The parameter `n` (`ξ' ∈ J + (n+1)|J|`, or `dis(ξ', J) ≥ n|J|`). -/
  n : ℕ
  /-- Whether `J` is the left or the right child of its parent. -/
  side : Side
  deriving DecidableEq

namespace Idx

/-- `m, n ∈ {1, 2, 3, 4}`, the range of [O+] (L1040-L1041). -/
def IsStd (ρ : Idx) : Prop := 1 ≤ ρ.m ∧ ρ.m ≤ 4 ∧ 1 ≤ ρ.n ∧ ρ.n ≤ 4

instance : DecidablePred IsStd := fun ρ => by unfold IsStd; infer_instance

/-- `ρ` is a 1-index or a 2-index (the indices for which the trees of Section 4 are defined,
L1206-L1259; the 3-indices are reduced to the 2-indices by reflection, L1099-L1121). -/
def IsOneOrTwo (ρ : Idx) : Prop := ρ.typ ≠ IdxType.three

/-- The finite interval `u - (m+1)|u|`, the set `ω_l` of a `1`- or `2`-index (L1074-L1076). -/
def ωlDyadic (ρ : Idx) (u : Dyadic) : Dyadic := u.shift (-((ρ.m : ℤ) + 1))

/-- The frequency set `ω_l` of the `ρ`-multitile with `ω_u = u` (L1074-L1082): `u - (m+1)|u|` for
`i = 1, 2`, and the half-line `(-∞, b - (m+1)|u|)` for `i = 3`, where `u = [a, b)`. -/
def ωl (ρ : Idx) (u : Dyadic) : Set ℝ :=
  match ρ.typ with
  | IdxType.one => (ρ.ωlDyadic u).toSet
  | IdxType.two => (ρ.ωlDyadic u).toSet
  | IdxType.three => Iio (u.right - ((ρ.m : ℝ) + 1) * u.length)

/-- The frequency set `ω_h` of the `ρ`-multitile with `ω_u = u` (L1074-L1082): `u + (n+1)|u|` for
`i = 1, 3`, and the half-line `[a + (n+1)|u|, ∞)` for `i = 2`, where `u = [a, b)`. -/
def ωh (ρ : Idx) (u : Dyadic) : Set ℝ :=
  match ρ.typ with
  | IdxType.one => (u.shift ((ρ.n : ℤ) + 1)).toSet
  | IdxType.two => Ici (u.left + ((ρ.n : ℝ) + 1) * u.length)
  | IdxType.three => (u.shift ((ρ.n : ℤ) + 1)).toSet

/-- Every point of `ω_l` lies to the left of `ω_u`. -/
theorem lt_left_of_mem_ωl (ρ : Idx) (u : Dyadic) {a : ℝ} (ha : a ∈ ρ.ωl u) : a < u.left := by
  have hL := u.length_pos
  have hm : (0 : ℝ) ≤ ρ.m := Nat.cast_nonneg _
  have hr := u.right_eq
  unfold ωl at ha
  cases h : ρ.typ <;> rw [h] at ha
  · simp only [ωlDyadic, Dyadic.toSet, Dyadic.right_shift, mem_Ico] at ha
    push_cast at ha
    nlinarith [ha.2]
  · simp only [ωlDyadic, Dyadic.toSet, Dyadic.right_shift, mem_Ico] at ha
    push_cast at ha
    nlinarith [ha.2]
  · simp only [mem_Iio] at ha
    nlinarith

/-- Every point of `ω_h` lies to the right of the left end point of `ω_u`. -/
theorem left_lt_of_mem_ωh (ρ : Idx) (u : Dyadic) {b : ℝ} (hb : b ∈ ρ.ωh u) : u.left < b := by
  have hL := u.length_pos
  have hn : (0 : ℝ) ≤ ρ.n := Nat.cast_nonneg _
  unfold ωh at hb
  cases h : ρ.typ <;> rw [h] at hb
  · simp only [Dyadic.toSet, Dyadic.left_shift, mem_Ico] at hb
    push_cast at hb
    nlinarith [hb.1]
  · simp only [mem_Ici] at hb
    nlinarith
  · simp only [Dyadic.toSet, Dyadic.left_shift, mem_Ico] at hb
    push_cast at hb
    nlinarith [hb.1]

/-- Every point of `ω_l` lies to the left of every point of `ω_h` (this is why the index `k` in the
definition of `a_P` at L1082 "would clearly be unique"). -/
theorem ωl_lt_ωh (ρ : Idx) (u : Dyadic) {a b : ℝ} (ha : a ∈ ρ.ωl u) (hb : b ∈ ρ.ωh u) : a < b :=
  (ρ.lt_left_of_mem_ωl u ha).trans (ρ.left_lt_of_mem_ωh u hb)

/-- The set `ω_l` is measurable. -/
theorem measurableSet_ωl (ρ : Idx) (u : Dyadic) : MeasurableSet (ρ.ωl u) := by
  unfold ωl
  split
  · exact Dyadic.measurableSet_toSet _
  · exact Dyadic.measurableSet_toSet _
  · exact measurableSet_Iio

/-- The set `ω_h` is measurable. -/
theorem measurableSet_ωh (ρ : Idx) (u : Dyadic) : MeasurableSet (ρ.ωh u) := by
  unfold ωh
  split
  · exact Dyadic.measurableSet_toSet _
  · exact measurableSet_Ici
  · exact Dyadic.measurableSet_toSet _

end Idx

/-- `J ∈ 𝒥_{ξ,ξ',ρ}` (L1046-L1051 of [O+]): `J` is a dyadic interval inside `(ξ, ξ')`, the
`side`-child of its dyadic parent, with `ξ ∈ ω_l(J)` and `ξ' ∈ ω_h(J)`. -/
def InClass (ρ : Idx) (ξ ξ' : ℝ) (J : Dyadic) : Prop :=
  J.toSet ⊆ Ioo ξ ξ' ∧ J.side = ρ.side ∧ ξ ∈ ρ.ωl J ∧ ξ' ∈ ρ.ωh J

/-! ### The set `R` and the neighbour index `i(ρ)` -/

/-- The ten indices of `R`, as an enumeration (named `r<i><m><n><L|R>`). -/
inductive RIdx where
  | r121L | r122L | r131L | r132L | r211L | r211R | r221R | r341L | r331R | r342L
  deriving DecidableEq

namespace RIdx

/-- The index `(i, m, n, side)` of an element of `R`. -/
def toIdx : RIdx → Idx
  | r121L => ⟨IdxType.one, 2, 1, Side.left⟩
  | r122L => ⟨IdxType.one, 2, 2, Side.left⟩
  | r131L => ⟨IdxType.one, 3, 1, Side.left⟩
  | r132L => ⟨IdxType.one, 3, 2, Side.left⟩
  | r211L => ⟨IdxType.two, 1, 1, Side.left⟩
  | r211R => ⟨IdxType.two, 1, 1, Side.right⟩
  | r221R => ⟨IdxType.two, 2, 1, Side.right⟩
  | r341L => ⟨IdxType.three, 4, 1, Side.left⟩
  | r331R => ⟨IdxType.three, 3, 1, Side.right⟩
  | r342L => ⟨IdxType.three, 4, 2, Side.left⟩

/-- The size ratio `i(ρ) ∈ {-1, 0, 1}` of L1054-L1057: the left Whitney neighbour `J'` of
`J ∈ 𝒥_{ξ,ξ',ρ}` has `|J'| = 2^{i(ρ)} |J|`. With `t = (a - ξ)/|J|` and `J = [a, b)`:
`J'` has size `|J|/2` if `t < 2`; for a right child size `|J|` if `t > 2`; for a left child size
`|J|` if `2 < t < 4` and `2|J|` if `t > 4` (and `ξ' - b < 2|J|`). The values are read off the
position conditions of `ρ`. -/
def i : RIdx → ℤ
  | r121L => 0
  | r122L => 0
  | r131L => 0
  | r132L => 0
  | r211L => -1
  | r211R => -1
  | r221R => 0
  | r341L => 1
  | r331R => 0
  | r342L => 1

/-- `i(ρ) ∈ {-1, 0, 1}`. -/
theorem i_mem (ρ : RIdx) : -1 ≤ ρ.i ∧ ρ.i ≤ 1 := by cases ρ <;> decide

/-- The indices of `R` have `m, n ∈ {1, …, 4}`. -/
theorem toIdx_isStd (ρ : RIdx) : ρ.toIdx.IsStd := by cases ρ <;> decide

end RIdx

/-- **The ten classes `𝒥_{ξ,ξ',ρ}`, `ρ ∈ R`, are pairwise disjoint** (first half of the conclusion
of [O+] L1054-L1057), for every `ξ, ξ'` and every dyadic `J`. -/
theorem inClass_disjoint {ρ ρ' : RIdx} (h : ρ ≠ ρ') (ξ ξ' : ℝ) (J : Dyadic) :
    ¬ (InClass ρ.toIdx ξ ξ' J ∧ InClass ρ'.toIdx ξ ξ' J) := by
  rintro ⟨⟨-, hs1, hl1, hh1⟩, ⟨-, hs2, hl2, hh2⟩⟩
  have hr := J.right_eq
  have hL := J.length_pos
  cases ρ <;> cases ρ' <;> try exact h rfl
  all_goals
    simp only [RIdx.toIdx, Idx.ωl, Idx.ωh, Idx.ωlDyadic, Dyadic.toSet, Dyadic.left_shift,
      Dyadic.right_shift, mem_Ico, mem_Iio, mem_Ici] at hl1 hh1 hl2 hh2 hs1 hs2
    first
      | (rw [hs1] at hs2; exact absurd hs2 (by decide))
      | (try push_cast at hl1 hh1 hl2 hh2
         try obtain ⟨hl1a, hl1b⟩ := hl1
         try obtain ⟨hh1a, hh1b⟩ := hh1
         try obtain ⟨hl2a, hl2b⟩ := hl2
         try obtain ⟨hh2a, hh2b⟩ := hh2
         linarith)

end PrimeCarleson.Proof.Oplus
