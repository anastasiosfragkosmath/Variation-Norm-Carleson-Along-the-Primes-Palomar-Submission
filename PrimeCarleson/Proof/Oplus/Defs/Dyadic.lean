module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Dyadic intervals and tiles of [O+]

The dyadic intervals `𝒟 = {[2^k m, 2^k (m+1)) : m, k ∈ ℤ}` and the tiles `I × ω` with
`|I||ω| = 1/2` ([O+], L924: "Let `𝒟 = …` be the set of
dyadic intervals. A tile will be any rectangle `I × ω` where `I, ω` are dyadic intervals, and
`|I||ω| = 1/2`"). Source: [O+], L930–L976 (dyadic intervals and tiles); the dyadic intervals also
serve the multitiles (`ω_l, ω_u, ω_h`, L1069–L1090), the trees (`I_𝒯 ⊂ [-2^{M_o}, 2^{M_o})`,
L1206–L1259) and the index set `R` (side-children, translates `J ± (m+1)|J|`, L1040–L1057).

* `Dyadic` is the pair `(k, m)` of integers; its set `toSet = [2^k m, 2^k (m+1))`, its `length`
  `2^k`, `left`, `right`, `center`, and `nested_or_disjoint`;
* `parent`, `child`, `side` (the "`side`-child of its dyadic parent", L1046-L1051), `shift` (the
  translate `J + j|J|`) and `dilate` (the dilate `C J` of a half-open interval with respect to its
  center, L1170: the dilate of `[a, b)` is the half-open interval of length `C(b - a)`
  with the same center; half-open is the convention under which `C₂ ω_u ∩ C₂ ω_l = ∅` holds for
  `C₂ = 2`, `m = 1`);
* points and containment: `ofPoint k x` (the dyadic interval of scale `k` containing `x`),
  `eq_of_k_eq_of_mem`, `k_le_of_toSet_subset`; the types `Dyadic`, `Tile` are
  countable;
* `Tile` with the area condition `I.k + J.k = -1`, equivalently `|I||J| = 1/2`
  (`Dyadic.area_iff`); the frequency interval of a tile is `J` (L976; L924 calls it `ω`).
-/

@[expose] public noncomputable section

open MeasureTheory Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- The two sides of a dyadic parent: "`J` is the `side`-child of its dyadic parent"
(L1046-L1051, L1073). -/
inductive Side where
  | left
  | right
  deriving DecidableEq

namespace Side

/-- The opposite side ("opposite side" at L1117). -/
def opp : Side → Side
  | left => right
  | right => left

/-- `0` for the left child, `1` for the right child. -/
def offset : Side → ℤ
  | left => 0
  | right => 1

/-- The opposite side of the opposite side is the side itself. -/
@[simp] theorem opp_opp (s : Side) : s.opp.opp = s := by cases s <;> rfl

/-- The offset of a side is nonnegative. -/
theorem offset_nonneg (s : Side) : 0 ≤ s.offset := by cases s <;> simp [offset]

/-- The offset of a side is at most `1`. -/
theorem offset_le_one (s : Side) : s.offset ≤ 1 := by cases s <;> simp [offset]

end Side

/-- A dyadic interval `[2^k m, 2^k (m+1))`, `k, m ∈ ℤ` (L924). -/
@[ext] structure Dyadic where
  /-- The scale: the length of the interval is `2^k`. -/
  k : ℤ
  /-- The position: the left end point is `2^k m`. -/
  m : ℤ
  deriving DecidableEq

namespace Dyadic

variable (I J : Dyadic)

/-- The length `|I| = 2^k`. -/
def length : ℝ := (2 : ℝ) ^ I.k

/-- The left end point `2^k m`. -/
def left : ℝ := (2 : ℝ) ^ I.k * I.m

/-- The right end point `2^k (m+1)`. -/
def right : ℝ := (2 : ℝ) ^ I.k * (I.m + 1)

/-- The center `c(I) = 2^k (m + 1/2)` (L976). -/
def center : ℝ := (2 : ℝ) ^ I.k * (I.m + 1 / 2)

/-- The half-open interval `[2^k m, 2^k (m+1))` as a set of reals. -/
def toSet : Set ℝ := Ico I.left I.right

/-- Dyadic intervals have positive length. -/
theorem length_pos : 0 < I.length := zpow_pos (by norm_num) _

/-- Dyadic intervals have nonzero length. -/
theorem length_ne_zero : I.length ≠ 0 := I.length_pos.ne'

/-- `right = left + length`. -/
theorem right_eq : I.right = I.left + I.length := by
  unfold right left length; ring

/-- `center = left + length / 2`. -/
theorem center_eq : I.center = I.left + I.length / 2 := by
  unfold center left length; ring

/-- `left < right`. -/
theorem left_lt_right : I.left < I.right := by
  rw [right_eq]; linarith [I.length_pos]

/-- Membership in `[left, right)`. -/
theorem mem_toSet {x : ℝ} : x ∈ I.toSet ↔ I.left ≤ x ∧ x < I.right := Iff.rfl

/-- The left end point lies in the interval. -/
theorem left_mem_toSet : I.left ∈ I.toSet := ⟨le_rfl, I.left_lt_right⟩

/-- A dyadic interval is nonempty. -/
theorem toSet_nonempty : I.toSet.Nonempty := ⟨_, I.left_mem_toSet⟩

/-- A dyadic interval is measurable. -/
theorem measurableSet_toSet : MeasurableSet I.toSet := measurableSet_Ico

/-- The Lebesgue measure `|I|` of the interval is its length. -/
theorem volume_toSet : volume I.toSet = ENNReal.ofReal I.length := by
  rw [toSet, Real.volume_Ico, right_eq]; congr 1; ring

/-- `|I||J| = 2^{k_I + k_J}`. -/
theorem length_mul_length : I.length * J.length = (2 : ℝ) ^ (I.k + J.k) := by
  unfold length; rw [zpow_add₀ (by norm_num)]

/-- The area condition `|I||ω| = 1/2` of a tile, in terms of the scales. -/
theorem area_iff : I.k + J.k = -1 ↔ I.length * J.length = 1 / 2 := by
  rw [length_mul_length]
  constructor
  · intro h; rw [h, zpow_neg_one]; norm_num
  · intro h
    have h2 : (2 : ℝ) ^ (I.k + J.k) = (2 : ℝ) ^ (-1 : ℤ) := by
      rw [h, zpow_neg_one]; norm_num
    exact zpow_right_injective₀ (by norm_num) (by norm_num) h2

/-! ### Nested or disjoint -/

/-- If `I` is not larger than `J`, then `I ⊆ J` or `I` and `J` are disjoint. -/
theorem toSet_subset_or_disjoint_of_k_le (h : I.k ≤ J.k) :
    I.toSet ⊆ J.toSet ∨ Disjoint I.toSet J.toSet := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, J.k = I.k + d := ⟨(J.k - I.k).toNat, by omega⟩
  have hpos : (0 : ℝ) < (2 : ℝ) ^ I.k := zpow_pos (by norm_num) _
  have hq : (2 : ℝ) ^ J.k = (2 : ℝ) ^ I.k * (((2 ^ d : ℤ)) : ℝ) := by
    rw [hd, zpow_add₀ (by norm_num)]; push_cast; simp
  have hqpos : (0 : ℤ) < 2 ^ d := by positivity
  have hJl : J.left = (2 : ℝ) ^ I.k * (((2 ^ d * J.m : ℤ)) : ℝ) := by
    unfold left; rw [hq]; push_cast; ring
  have hJr : J.right = (2 : ℝ) ^ I.k * (((2 ^ d * (J.m + 1) : ℤ)) : ℝ) := by
    unfold right; rw [hq]; push_cast; ring
  have hIl : I.left = (2 : ℝ) ^ I.k * (I.m : ℝ) := rfl
  have hIr : I.right = (2 : ℝ) ^ I.k * (((I.m + 1 : ℤ)) : ℝ) := by
    unfold right; push_cast; rfl
  rcases lt_or_ge I.m (2 ^ d * J.m) with h1 | h1
  · right
    refine Set.disjoint_left.2 fun x hx hxJ => ?_
    have h1' : ((I.m + 1 : ℤ) : ℝ) ≤ (((2 ^ d * J.m : ℤ)) : ℝ) := by exact_mod_cast h1
    have := mul_le_mul_of_nonneg_left h1' hpos.le
    rw [← hIr, ← hJl] at this
    exact absurd (lt_of_lt_of_le hx.2 this) (not_lt.2 hxJ.1)
  · rcases lt_or_ge I.m (2 ^ d * (J.m + 1)) with h2 | h2
    · left
      intro x hx
      have h1' : (((2 ^ d * J.m : ℤ)) : ℝ) ≤ (I.m : ℝ) := by exact_mod_cast h1
      have h2' : ((I.m + 1 : ℤ) : ℝ) ≤ (((2 ^ d * (J.m + 1) : ℤ)) : ℝ) := by exact_mod_cast h2
      have h3 := mul_le_mul_of_nonneg_left h1' hpos.le
      have h4 := mul_le_mul_of_nonneg_left h2' hpos.le
      rw [← hIl, ← hJl] at h3
      rw [← hIr, ← hJr] at h4
      exact ⟨h3.trans hx.1, lt_of_lt_of_le hx.2 h4⟩
    · right
      refine Set.disjoint_left.2 fun x hx hxJ => ?_
      have h2' : (((2 ^ d * (J.m + 1) : ℤ)) : ℝ) ≤ (I.m : ℝ) := by exact_mod_cast h2
      have := mul_le_mul_of_nonneg_left h2' hpos.le
      rw [← hIl, ← hJr] at this
      exact absurd (lt_of_lt_of_le hxJ.2 this) (not_lt.2 hx.1)

/-- Two dyadic intervals are nested or disjoint. -/
theorem nested_or_disjoint :
    I.toSet ⊆ J.toSet ∨ J.toSet ⊆ I.toSet ∨ Disjoint I.toSet J.toSet := by
  rcases le_total I.k J.k with h | h
  · rcases I.toSet_subset_or_disjoint_of_k_le J h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases J.toSet_subset_or_disjoint_of_k_le I h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.symm)

/-! ### Parent and children -/

/-- The dyadic parent `[2^{k+1} ⌊m/2⌋, 2^{k+1} (⌊m/2⌋ + 1))` of `I`. -/
def parent : Dyadic := ⟨I.k + 1, I.m / 2⟩

/-- The `s`-child of `I`: the left (`s = left`) or right half of `I`. -/
def child (s : Side) : Dyadic := ⟨I.k - 1, 2 * I.m + s.offset⟩

/-- Whether `I` is the left or the right child of its parent: `left` iff `m` is even. -/
def side : Side := if I.m % 2 = 0 then Side.left else Side.right

/-- The parent has scale `k + 1`. -/
@[simp] theorem parent_k : I.parent.k = I.k + 1 := rfl

/-- A child has scale `k - 1`. -/
@[simp] theorem child_k (s : Side) : (I.child s).k = I.k - 1 := rfl

/-- The parent has twice the length. -/
theorem length_parent : I.parent.length = 2 * I.length := by
  unfold length parent; simp only; rw [zpow_add_one₀ (by norm_num)]; ring

/-- A child has half the length. -/
theorem length_child (s : Side) : (I.child s).length = I.length / 2 := by
  unfold length child; simp only; rw [zpow_sub_one₀ (by norm_num)]; ring

/-- A dyadic interval lies in its parent. -/
theorem toSet_subset_parent : I.toSet ⊆ I.parent.toSet := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  have hm1 : 2 * (I.m / 2) ≤ I.m := by omega
  have hm2 : I.m + 1 ≤ 2 * (I.m / 2 + 1) := by omega
  have hpos : (0 : ℝ) < (2 : ℝ) ^ I.k := zpow_pos (by norm_num) _
  have h2k : (2 : ℝ) ^ (I.k + 1) = 2 * (2 : ℝ) ^ I.k := by
    rw [zpow_add_one₀ (by norm_num)]; ring
  have hm1' : (2 : ℝ) * ((I.m / 2 : ℤ) : ℝ) ≤ I.m := by exact_mod_cast hm1
  have hm2' : (I.m : ℝ) + 1 ≤ 2 * (((I.m / 2 : ℤ) : ℝ) + 1) := by exact_mod_cast hm2
  constructor
  · change (2 : ℝ) ^ (I.k + 1) * ((I.m / 2 : ℤ) : ℝ) ≤ x
    rw [h2k]
    calc 2 * (2 : ℝ) ^ I.k * ((I.m / 2 : ℤ) : ℝ) = (2 : ℝ) ^ I.k * (2 * ((I.m / 2 : ℤ) : ℝ)) := by
          ring
      _ ≤ (2 : ℝ) ^ I.k * I.m := mul_le_mul_of_nonneg_left hm1' hpos.le
      _ ≤ x := h1
  · change x < (2 : ℝ) ^ (I.k + 1) * (((I.m / 2 : ℤ) : ℝ) + 1)
    rw [h2k]
    calc x < (2 : ℝ) ^ I.k * ((I.m : ℝ) + 1) := h2
      _ ≤ (2 : ℝ) ^ I.k * (2 * (((I.m / 2 : ℤ) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hm2' hpos.le
      _ = 2 * (2 : ℝ) ^ I.k * (((I.m / 2 : ℤ) : ℝ) + 1) := by ring

/-- The parent of the `s`-child of `I` is `I`. -/
@[simp] theorem parent_child (s : Side) : (I.child s).parent = I := by
  have h : (2 * I.m + s.offset) / 2 = I.m := by
    have := s.offset_nonneg
    have := s.offset_le_one
    omega
  ext
  · simp [parent, child]
  · simp [parent, child, h]

/-- The `s`-child of `I` is the `s`-child of its parent. -/
@[simp] theorem side_child (s : Side) : (I.child s).side = s := by
  have h : (2 * I.m + s.offset) % 2 = s.offset := by
    have := s.offset_nonneg
    have := s.offset_le_one
    omega
  cases s <;> simp [side, child, Side.offset]

/-- `I` is the `side`-child of its dyadic parent. -/
@[simp] theorem child_parent_side : I.parent.child I.side = I := by
  ext
  · simp [parent, child]
  · simp only [parent, child, side]
    split_ifs with h <;> simp [Side.offset] <;> omega

/-! ### Translates and dilates -/

/-- The translate `I + j |I|`, again a dyadic interval of the same scale. -/
def shift (j : ℤ) : Dyadic := ⟨I.k, I.m + j⟩

/-- A translate `I + j|I|` has the scale of `I`. -/
@[simp] theorem shift_k (j : ℤ) : (I.shift j).k = I.k := rfl

/-- A translate `I + j|I|` has the length of `I`. -/
theorem length_shift (j : ℤ) : (I.shift j).length = I.length := rfl

/-- The left end point of `I + j|I|`. -/
theorem left_shift (j : ℤ) : (I.shift j).left = I.left + j * I.length := by
  unfold left shift length; simp only; push_cast; ring

/-- The right end point of `I + j|I|`. -/
theorem right_shift (j : ℤ) : (I.shift j).right = I.right + j * I.length := by
  unfold right shift length; simp only; push_cast; ring

/-- The center of `I + j|I|`. -/
theorem center_shift (j : ℤ) : (I.shift j).center = I.center + j * I.length := by
  unfold center shift length; simp only; push_cast; ring

/-- `x ∈ I + j|I|` iff `x - j|I| ∈ I`. -/
theorem mem_shift_toSet {x : ℝ} (j : ℤ) : x ∈ (I.shift j).toSet ↔ x - j * I.length ∈ I.toSet := by
  simp only [mem_toSet, left_shift, right_shift]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The dilate `C I` of a half-open interval with respect to its center (L1170): the half-open
interval with the center of `I` and length `C |I|`. -/
def dilate (C : ℝ) : Set ℝ := Ico (I.center - C * I.length / 2) (I.center + C * I.length / 2)

/-- The dilate by `1` is the interval itself. -/
theorem dilate_one : I.dilate 1 = I.toSet := by
  rw [dilate, toSet, center_eq, right_eq]
  congr 1 <;> ring

/-- Dilates are monotone in the factor. -/
theorem dilate_mono {C C' : ℝ} (h : C ≤ C') : I.dilate C ⊆ I.dilate C' := by
  have := I.length_pos
  exact Ico_subset_Ico (by nlinarith) (by nlinarith)

/-- The interval lies in its dilates by factors `≥ 1`. -/
theorem toSet_subset_dilate {C : ℝ} (h : 1 ≤ C) : I.toSet ⊆ I.dilate C := by
  rw [← dilate_one]; exact dilate_mono I h

/-- The center of `I` lies in `I`. -/
theorem center_mem_toSet : I.center ∈ I.toSet := by
  have := I.length_pos
  rw [mem_toSet, center_eq, right_eq]
  constructor <;> linarith

/-- There are countably many dyadic intervals (`Dyadic ≃ ℤ × ℤ`). -/
instance : Countable Dyadic :=
  Function.Injective.countable (f := fun I : Dyadic => (I.k, I.m))
    (fun _ _ h => Dyadic.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-! ### Scales, points and containment -/

/-- The position `m` of a dyadic interval containing `x` is `⌊x / 2^k⌋`. -/
theorem m_eq_floor {x : ℝ} (hx : x ∈ I.toSet) : I.m = ⌊x / (2 : ℝ) ^ I.k⌋ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ I.k := zpow_pos (by norm_num) _
  rw [eq_comm, Int.floor_eq_iff]
  obtain ⟨h1, h2⟩ := hx
  simp only [left, right] at h1 h2
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-- Two dyadic intervals of the same scale that share a point are equal. -/
theorem eq_of_k_eq_of_mem {I J : Dyadic} (hk : I.k = J.k) {x : ℝ} (hI : x ∈ I.toSet)
    (hJ : x ∈ J.toSet) : I = J := by
  have h1 := I.m_eq_floor hI
  have h2 := J.m_eq_floor hJ
  rw [← hk] at h2
  exact Dyadic.ext hk (h1.trans h2.symm)

/-- The dyadic interval of scale `k` containing `x`: `[2^k ⌊x/2^k⌋, 2^k (⌊x/2^k⌋ + 1))`. -/
def ofPoint (k : ℤ) (x : ℝ) : Dyadic := ⟨k, ⌊x / (2 : ℝ) ^ k⌋⟩

/-- `x` lies in the dyadic interval of scale `k` containing `x`. -/
theorem mem_toSet_ofPoint (k : ℤ) (x : ℝ) : x ∈ (ofPoint k x).toSet := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have h1 := Int.floor_le (x / (2 : ℝ) ^ k)
  have h2 := Int.lt_floor_add_one (x / (2 : ℝ) ^ k)
  rw [le_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  constructor
  · change (2 : ℝ) ^ k * ((⌊x / (2 : ℝ) ^ k⌋ : ℤ) : ℝ) ≤ x
    linarith
  · change x < (2 : ℝ) ^ k * (((⌊x / (2 : ℝ) ^ k⌋ : ℤ) : ℝ) + 1)
    linarith

/-- A dyadic interval of scale `k` containing `x` is `ofPoint k x`. -/
theorem eq_ofPoint_of_mem {I : Dyadic} {x : ℝ} (hx : x ∈ I.toSet) : I = ofPoint I.k x :=
  eq_of_k_eq_of_mem rfl hx (mem_toSet_ofPoint I.k x)

/-- Containment of dyadic intervals forces the scale to go up: `I ⊆ J → k_I ≤ k_J`. -/
theorem k_le_of_toSet_subset {I J : Dyadic} (h : I.toSet ⊆ J.toSet) : I.k ≤ J.k := by
  have h1 : volume I.toSet ≤ volume J.toSet := measure_mono h
  rw [volume_toSet, volume_toSet, ENNReal.ofReal_le_ofReal_iff J.length_pos.le] at h1
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h1

/-- A dyadic interval is contained in a dyadic interval of the same scale iff they are equal. -/
theorem eq_of_toSet_subset_of_k_eq {I J : Dyadic} (hk : I.k = J.k) (h : I.toSet ⊆ J.toSet) :
    I = J :=
  eq_of_k_eq_of_mem hk I.left_mem_toSet (h I.left_mem_toSet)

end Dyadic

/-- A *tile* is a rectangle `I × J` with `I, J` dyadic and `|I||J| = 1/2` (L924, where the
frequency interval is called `ω`; L976 calls it `J`); the area condition is stated on the scales,
`I.k + J.k = -1` (see `Dyadic.area_iff`). -/
@[ext] structure Tile where
  /-- The time interval. -/
  I : Dyadic
  /-- The frequency interval. -/
  J : Dyadic
  /-- The area condition `|I||J| = 1/2`. -/
  area : I.k + J.k = -1
  deriving DecidableEq

namespace Tile

end Tile

/-- There are countably many tiles. -/
instance : Countable Tile :=
  Function.Injective.countable (f := fun P : Tile => (P.I, P.J))
    (fun _ _ h => Tile.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

end PrimeCarleson.Proof.Oplus
