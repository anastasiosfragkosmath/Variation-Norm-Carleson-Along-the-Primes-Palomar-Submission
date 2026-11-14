/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/NaturalScaleIntegerWindow.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]

noncomputable def centeredIntegerBox (R : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (-(R i : ℤ)) (R i : ℤ))

@[simp] theorem mem_centeredIntegerBox (R : ι → ℕ) (x : ι → ℤ) :
    x ∈ centeredIntegerBox R ↔ ∀ i, |x i| ≤ (R i : ℤ) := by
  simp only [centeredIntegerBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

@[simp] theorem card_centeredIntegerBox (R : ι → ℕ) :
    (centeredIntegerBox R).card = ∏ i, (2 * R i + 1) := by
  rw [centeredIntegerBox, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.card_Icc]
  omega

theorem card_doubled_centeredIntegerBox_le (R : ι → ℕ) :
    (centeredIntegerBox (fun i => 2 * R i)).card ≤
      2 ^ Fintype.card ι * (centeredIntegerBox R).card := by
  rw [card_centeredIntegerBox, card_centeredIntegerBox]
  calc
    (∏ i, (2 * (2 * R i) + 1)) ≤ ∏ i, (2 * (2 * R i + 1)) := by
      gcongr with i
      omega
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

omit [Fintype ι] [DecidableEq ι] in
theorem card_mul_le_of_kernel_translates (φ : (ι → ℤ) →+ G)
    (S X : Finset (ι → ℤ)) (k : ℕ) (v : ι → ℤ) (hv : v ≠ 0)
    (hker : φ v = 0) (hinj : Set.InjOn φ (S : Set _))
    (hsub : ∀ x ∈ S, ∀ j < k, x + j • v ∈ X) : S.card * k ≤ X.card := by
  classical
  rw [← Finset.card_range k, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun z : (ι → ℤ) × ℕ => z.1 + z.2 • v)
  · intro z hz
    exact hsub z.1 (Finset.mem_product.mp hz).1 z.2
      (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  · intro x hx y hy hxy
    change x.1 + x.2 • v = y.1 + y.2 • v at hxy
    have hφ : φ x.1 = φ y.1 := by
      have h := congrArg φ hxy
      simpa only [map_add, map_nsmul, hker, nsmul_zero, add_zero] using h
    have hbase : x.1 = y.1 := hinj (Finset.mem_product.mp hx).1
      (Finset.mem_product.mp hy).1 hφ
    apply Prod.ext hbase
    have hmul : x.2 • v = y.2 • v := by
      rw [hbase] at hxy
      exact add_left_cancel hxy
    have hnonzero : ¬ ∀ i, v i = 0 := fun h => hv (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnonzero
    have hiEq := congrFun hmul i
    simp only [Pi.smul_apply, nsmul_eq_mul] at hiEq
    exact_mod_cast mul_right_cancel₀ hi hiEq

theorem kernel_eq_zero_of_dense_integer_box (φ : (ι → ℤ) →+ G)
    (S : Finset (ι → ℤ)) (R : ι → ℕ) (k : ℕ)
    (hS : S ⊆ centeredIntegerBox R) (hinj : Set.InjOn φ (S : Set _))
    (hlarge : (centeredIntegerBox (fun i => 2 * R i)).card < S.card * k)
    (v : ι → ℤ) (hker : φ v = 0) (hshort : ∀ i, (k : ℤ) * |v i| ≤ (R i : ℤ)) :
    v = 0 := by
  by_contra hv
  apply (not_le_of_gt hlarge)
  apply card_mul_le_of_kernel_translates φ S (centeredIntegerBox (fun i => 2 * R i)) k v hv hker hinj
  intro x hx j hj
  apply (mem_centeredIntegerBox _ _).mpr
  intro i
  have hxi := (mem_centeredIntegerBox R x).mp (hS hx) i
  have hjk : (j : ℤ) ≤ k := by exact_mod_cast hj.le
  have hbound : |x i + (j : ℤ) * v i| ≤ 2 * (R i : ℤ) := by
    calc
      _ ≤ |x i| + |(j : ℤ) * v i| := abs_add_le _ _
      _ = |x i| + (j : ℤ) * |v i| := by
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg j)]
      _ ≤ (R i : ℤ) + (k : ℤ) * |v i| :=
        add_le_add hxi (mul_le_mul_of_nonneg_right hjk (abs_nonneg _))
      _ ≤ 2 * (R i : ℤ) := by linarith only [hshort i]
  change |x i + j • v i| ≤ ((2 * R i : ℕ) : ℤ)
  simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hbound

theorem injOn_small_integer_box_of_dense_subset (φ : (ι → ℤ) →+ G)
    (S : Finset (ι → ℤ)) (R r : ι → ℕ) (k : ℕ)
    (hS : S ⊆ centeredIntegerBox R) (hinj : Set.InjOn φ (S : Set _))
    (hlarge : (centeredIntegerBox (fun i => 2 * R i)).card < S.card * k)
    (hscale : ∀ i, 2 * k * r i ≤ R i) :
    Set.InjOn φ (centeredIntegerBox r : Set _) := by
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  apply kernel_eq_zero_of_dense_integer_box φ S R k hS hinj hlarge (x - y)
  · rw [map_sub, hxy, sub_self]
  · intro i
    have hx' := (mem_centeredIntegerBox r x).mp hx i
    have hy' := (mem_centeredIntegerBox r y).mp hy i
    have hscale' : 2 * (k : ℤ) * (r i : ℤ) ≤ R i := by exact_mod_cast hscale i
    calc
      (k : ℤ) * |(x - y) i| ≤ (k : ℤ) * (|x i| + |y i|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Int.natCast_nonneg k)
      _ ≤ (k : ℤ) * ((r i : ℤ) + (r i : ℤ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hx' hy') (Int.natCast_nonneg k)
      _ = 2 * (k : ℤ) * (r i : ℤ) := by ring
      _ ≤ (R i : ℤ) := hscale'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem injOn_shrunk_integer_box_of_distinct_points
    {r : ℕ} {G : Type*} [AddCommGroup G] (J : Finset G) (hJ : J.Nonempty)
    (R : Fin r → ℕ) (η : (Fin r → ℤ) →+ G) (a : G)
    (hrepr : ∀ h ∈ J, ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = a + η x) :
    let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J.card + 1
    Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) := by
  intro k
  classical
  have hall (h : {h // h ∈ J}) : ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ h.val = a + η x :=
    hrepr h.val h.property
  choose x hx heq using hall
  have hηx : Function.Injective (η ∘ x) := by
    intro h h' hh
    apply Subtype.ext
    rw [heq h, heq h']
    exact congrArg (fun z => a + z) hh
  have hxinj : Function.Injective x := by
    intro h h' hh
    exact hηx (congrArg η hh)
  let S := Finset.univ.image x
  have hS : S ⊆ centeredIntegerBox R := by
    intro z hz
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_centeredIntegerBox R (x h)).mpr (hx h)
  have hScard : S.card = J.card := by
    rw [show S.card = (Finset.univ.image x).card from rfl,
      Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_coe]
  have hinj : Set.InjOn η (S : Set _) := by
    intro z hz w hw hzw
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h', _, rfl⟩ := Finset.mem_image.mp hw
    exact congrArg x (hηx hzw)
  apply injOn_small_integer_box_of_dense_subset η S R (fun i => R i / (2 * k)) k hS hinj
  · apply (card_doubled_centeredIntegerBox_le R).trans_lt
    rw [card_centeredIntegerBox, Fintype.card_fin, hScard]
    exact Nat.lt_mul_div_succ (2 ^ r * ∏ i, (2 * R i + 1)) hJ.card_pos
  · intro i
    exact Nat.mul_div_le (R i) (2 * k)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI
