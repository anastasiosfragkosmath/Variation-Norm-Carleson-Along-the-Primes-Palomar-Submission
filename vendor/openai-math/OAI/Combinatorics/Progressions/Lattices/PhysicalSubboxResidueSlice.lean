/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/PhysicalSubboxResidueSlice.lean
Changes: Lean module/public-import conversion, removal of unneeded declarations and imports, plus compatibility
edits for Lean 4.35 and its Mathlib (vendor/provenance/openai-progressions-files.json).
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CubeTranslation
public import OAI.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
public import OAI.Combinatorics.Progressions.Estimates.PhysicalSliceCost
public import OAI.Combinatorics.Progressions.Estimates.WeightedOverlapCorrelation
public import OAI.Combinatorics.Progressions.Geometry.BoxBlockBudget
public import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
public import OAI.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
@[expose] public section

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def integerBox (T : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i ↦ Finset.Ico (0 : ℤ) (T i))

@[simp] theorem mem_integerBox (T : ι → ℕ) (x : ι → ℤ) :
    x ∈ integerBox T ↔ ∀ i, 0 ≤ x i ∧ x i < T i := by
  simp [integerBox, Fintype.mem_piFinset]

omit [Fintype ι] [DecidableEq ι] in
theorem int_eq_of_zmod_eq_of_bounds {m : ℕ} {a b : ℤ}
    (ha : 0 ≤ a ∧ a < m) (hb : 0 ≤ b ∧ b < m) (he : (a : ZMod m) = (b : ZMod m)) :
    a = b := by
  have hm := (ZMod.intCast_eq_intCast_iff' a b m).mp he
  simpa only [Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] using hm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBox_expect_eq_zmod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) [NeZero N] (f : (ι → ℤ) → ℂ) :
    (𝔼 x ∈ integerBox (fun _ : ι => N), f x) =
      𝔼 t : ι → ZMod N, f (fun i => ((t i).val : ℤ)) := by
  symm
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    rw [mem_integerBox]
    exact fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).val_lt⟩
  · intro t _
    rfl
  · intro t _ u _ h
    funext i
    apply ZMod.val_injective N
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox (fun _ : ι => N) x).mp hx
    refine ⟨(fun i => (x i : ZMod N)), Finset.mem_univ _, ?_⟩
    funext i
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hx' i).1 (hx' i).2]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

def integerCyclicMap (N : ℕ) : ℤ →+ ZMod N := Int.castAddHom (ZMod N)

theorem integerInterval_reflectsPairSums (N : ℕ) (a b : ℤ)
    (hdiam : 2 * (b - a - 1) < (N : ℤ)) :
    ReflectsPairSums (integerCyclicMap N) (Finset.Ico a b : Set ℤ) := by
  intro x hx y hy z hz t ht he
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  have hz' := Finset.mem_Ico.mp hz
  have ht' := Finset.mem_Ico.mp ht
  have hxy : 0 ≤ x + y - 2 * a ∧ x + y - 2 * a < N := by omega
  have hzt : 0 ≤ z + t - 2 * a ∧ z + t - 2 * a < N := by omega
  have he' : ((x + y - 2 * a : ℤ) : ZMod N) = ((z + t - 2 * a : ℤ) : ZMod N) := by
    change (x : ZMod N) + y = (z : ZMod N) + t at he
    push_cast
    exact congrArg (fun v : ZMod N => v - 2 * (a : ZMod N)) he
  have hh := int_eq_of_zmod_eq_of_bounds hxy hzt he'
  omega

theorem integerInterval_image_cyclicInterval (N : ℕ) (a : ℤ) (L : ℕ) :
    (Finset.Ico a (a + L)).image (integerCyclicMap N) = cyclicInterval (a : ZMod N) L := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_Ico.mp hy
    refine Finset.mem_image.mpr ⟨(y - a).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · change (a : ZMod N) + ((y - a).toNat : ZMod N) = (y : ZMod N)
      have he : (((y - a).toNat : ℕ) : ℤ) = y - a := Int.toNat_of_nonneg (by omega)
      rw [← Int.cast_natCast, he]
      push_cast
      ring
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨a + k, Finset.mem_Ico.mpr ?_, ?_⟩
    · have hk' := Finset.mem_range.mp hk
      omega
    · change ((a + k : ℤ) : ZMod N) = (a : ZMod N) + k
      push_cast
      rfl

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem integerBox_nonempty : (integerBox T).Nonempty := by
  refine ⟨0, (mem_integerBox T 0).mpr ?_⟩
  intro i
  change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < T i
  exact ⟨le_rfl, by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (T i))⟩

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_integerBox (T : ι → ℕ) : (integerBox T).card = ∏ i, T i := by
  simp [integerBox]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) : Finset (ι → ℤ) :=
  translateSupport a (integerBox T)

theorem mem_translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) (x : ι → ℤ) :
    x ∈ translatedIntegerBox a T ↔ ∀ i, a i ≤ x i ∧ x i < a i + T i := by
  rw [translatedIntegerBox, mem_translateSupport, mem_integerBox]
  apply forall_congr'
  intro i
  change (0 ≤ x i - a i ∧ x i - a i < T i) ↔ _
  omega

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem translatedIntegerBox_nonempty (a : ι → ℤ) : (translatedIntegerBox a T).Nonempty :=
  (integerBox_nonempty T).image (fun x ↦ a + x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivativeSupport_translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) (h : ι → ℤ) :
    derivativeSupport (translatedIntegerBox a T) h =
      translatedIntegerBox (fun i => a i + max 0 (-h i)) (fun i => ((T i : ℤ) - |h i|).toNat) := by
  ext x
  simp only [derivativeSupport, Finset.mem_filter, mem_translatedIntegerBox, Pi.add_apply,
    ← forall_and]
  apply forall_congr'
  intro i
  by_cases hi : 0 ≤ h i
  · rw [abs_of_nonneg hi, max_eq_left (by omega : -h i ≤ 0)]
    omega
  · rw [abs_of_neg (by omega : h i < 0), max_eq_right (by omega : 0 ≤ -h i)]
    omega

theorem box_overlap_length_pos (a : ι → ℤ) (T : ι → ℕ) {h : ι → ℤ}
    (hh : h ∈ cubeDifferenceSupport (translatedIntegerBox a T)) (i : ι) :
    0 < ((T i : ℤ) - |h i|).toNat := by
  obtain ⟨x, hx⟩ := (mem_cubeDifferenceSupport _ h).mp hh
  obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
  have hx' := (mem_translatedIntegerBox a T x).mp hx i
  have hxh' := (mem_translatedIntegerBox a T (x + h)).mp hxh i
  simp only [Pi.add_apply] at hxh'
  by_cases hi : 0 ≤ h i
  · rw [abs_of_nonneg hi]
    omega
  · rw [abs_of_neg (by omega : h i < 0)]
    omega

theorem box_differenceSupport_subset (a : ι → ℤ) (T : ι → ℕ) :
    cubeDifferenceSupport (translatedIntegerBox a T) ⊆
      translatedIntegerBox (fun i => -(T i : ℤ)) (fun i => 2 * T i) := by
  intro h hh
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  apply (mem_translatedIntegerBox _ _ _).mpr
  intro i
  have hx' := (mem_translatedIntegerBox a T p.1).mp hx i
  have hy' := (mem_translatedIntegerBox a T p.2).mp hy i
  simp only [Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat]
  omega

theorem card_box_differenceSupport_le (a : ι → ℤ) (T : ι → ℕ) :
    (cubeDifferenceSupport (translatedIntegerBox a T)).card ≤
      2 ^ Fintype.card ι * (translatedIntegerBox a T).card := by
  apply (Finset.card_le_card (box_differenceSupport_subset a T)).trans_eq
  simp only [translatedIntegerBox, card_translateSupport, card_integerBox,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice

variable {X : Type*} (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))

end ResidueBoxSlice
end Erdos3

end

end OAI
