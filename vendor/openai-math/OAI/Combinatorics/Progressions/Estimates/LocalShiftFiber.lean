/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/LocalShiftFiber.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import OAI.Combinatorics.Progressions.Sampling.FiniteSamplingMoment
@[expose] public section

namespace OAI

section

namespace Erdos3

open Finset Fintype
open scoped BigOperators Pointwise

namespace CyclicCrootSisask

variable {N k m : ℕ} [NeZero N]

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

section LargeShifts

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {A S : Finset G} {r : ℕ}

end LargeShifts

noncomputable def setAverageTranslate
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x : ZMod N) : ℝ :=
  (∑ a ∈ A, f (x - a)) / A.card

noncomputable def centeredTranslate
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x a : ZMod N) : ℝ :=
  f (x - a) - setAverageTranslate A f x

noncomputable def sampleDeviation
    (A : Finset (ZMod N)) (f : ZMod N → ℝ)
    (a : Fin k → ZMod N) (x : ZMod N) : ℝ :=
  ∑ i, centeredTranslate A f x (a i)

omit [NeZero N] in
lemma sum_centeredTranslate_eq_zero
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ) (x : ZMod N) :
    ∑ a ∈ A, centeredTranslate A f x a = 0 := by
  have hcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hA
  unfold centeredTranslate setAverageTranslate
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

omit [NeZero N] in

theorem pointwise_sampleDeviation_moment
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    (hm : m ≠ 0) (x : ZMod N) :
    ∑ a ∈ A ^^ k, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
  let g : ZMod N → ℝ := centeredTranslate A f x
  have hg : ∀ i, ∑ a ∈ A ^^ k, g (a i) = 0 := by
    intro i
    rw [Fintype.sum_piFinset_apply]
    rw [show ∑ b ∈ A, g b = 0 by
      simpa [g] using sum_centeredTranslate_eq_zero hA f x]
    simp
  have h := Erdos3.CyclicMZ.RCLike.marcinkiewicz_zygmund
    (A := A) (n := k) hm g hg
  simpa only [Real.norm_eq_abs, sampleDeviation, g] using h

theorem global_sampleDeviation_moment
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    (hm : m ≠ 0) :
    ∑ a ∈ A ^^ k, ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
  rw [Finset.sum_comm]
  calc
    ∑ x : ZMod N, ∑ a ∈ A ^^ k, |sampleDeviation A f a x| ^ (2 * m) ≤
        ∑ x : ZMod N, (8 * m) ^ m * k ^ (m - 1) *
          ∑ a ∈ A ^^ k, ∑ i,
            |centeredTranslate A f x (a i)| ^ (2 * m) := by
      exact Finset.sum_le_sum fun x _ ↦ pointwise_sampleDeviation_moment hA f hm x
    _ = (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

omit [NeZero N] in

lemma abs_setAverageTranslate_le
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    {M : ℝ} (_ : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (x : ZMod N) :
    |setAverageTranslate A f x| ≤ M := by
  have hcard : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hsum : ∑ a ∈ A, |f (x - a)| ≤ ∑ _a ∈ A, M := by
    exact Finset.sum_le_sum fun a _ ↦ hf (x - a)
  unfold setAverageTranslate
  calc
    |(∑ a ∈ A, f (x - a)) / (A.card : ℝ)| =
        |∑ a ∈ A, f (x - a)| / (A.card : ℝ) := by
      rw [abs_div, abs_of_pos hcard]
    _ ≤ (∑ a ∈ A, |f (x - a)|) / (A.card : ℝ) := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ (∑ _a ∈ A, M) / (A.card : ℝ) := by gcongr
    _ = M := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

lemma markov_card_good
    {ι : Type*} {S : Finset ι} {g : ι → ℝ} {c ε : ℝ}
    (hc : 0 < c) (hg : ∀ a ∈ S, 0 ≤ g a)
    (h : ∑ a ∈ S, g a ≤ ε * c * S.card) :
    (1 - ε) * S.card ≤ (S.filter fun a ↦ g a ≤ c).card := by
  classical
  have hbad := h.trans'
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun a ↦ ¬g a ≤ c) S) fun i hi _ ↦ hg i hi)
  have hcount :=
    (Finset.card_nsmul_le_sum (S.filter fun a ↦ ¬g a ≤ c) g c
      (by simp +contextual [le_of_lt])).trans hbad
  rw [nsmul_eq_mul, mul_right_comm] at hcount
  have hcount' := le_of_mul_le_mul_right hcount hc
  rw [Finset.filter_not, Finset.cast_card_sdiff (Finset.filter_subset _ _)] at hcount'
  linarith

noncomputable def goodSamples
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (k m : ℕ) (C : ℝ) :
    Finset (Fin k → ZMod N) :=
  (A ^^ k).filter fun a ↦
    (∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m)) ≤ C

lemma mem_goodSamples
    {A : Finset (ZMod N)} {f : ZMod N → ℝ} {C : ℝ}
    {a : Fin k → ZMod N} :
    a ∈ goodSamples A f k m C ↔
      a ∈ A ^^ k ∧
        (∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m)) ≤ C := by
  simp [goodSamples]

omit [NeZero N] in
lemma sampleDeviation_sub_const_identity
    (A : Finset (ZMod N)) (f : ZMod N → ℝ)
    (a : Fin k → ZMod N) (t x : ZMod N) :
    sampleDeviation A f (a - fun _ ↦ t) x -
        sampleDeviation A f a (x + t) =
      (k : ℝ) *
        (setAverageTranslate A f (x + t) - setAverageTranslate A f x) := by
  unfold sampleDeviation centeredTranslate
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  have harg (i : Fin k) : x - (a i - t) = x + t - a i := by abel
  simp_rw [harg]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

theorem goodSamples_give_almost_period
    {A : Finset (ZMod N)} {f : ZMod N → ℝ} {C : ℝ}
    {a : Fin k → ZMod N} {t : ZMod N}
    (ha : a ∈ goodSamples A f k m C)
    (hat : (a - fun _ ↦ t) ∈ goodSamples A f k m C) :
    (k : ℝ) ^ (2 * m) *
        ∑ x : ZMod N,
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
      2 ^ (2 * m) * C := by
  have haMoment := (mem_goodSamples (N := N) (k := k) (m := m)).1 ha |>.2
  have hatMoment := (mem_goodSamples (N := N) (k := k) (m := m)).1 hat |>.2
  have hshift :
      (∑ x : ZMod N, |sampleDeviation A f a (x + t)| ^ (2 * m)) =
        ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) := by
    exact Fintype.sum_equiv (Equiv.addRight t) _ _ fun _ ↦ rfl
  by_cases hm : m = 0
  · subst m
    simpa using haMoment
  have hpne : 2 * m ≠ 0 := mul_ne_zero two_ne_zero hm
  calc
    (k : ℝ) ^ (2 * m) *
        ∑ x : ZMod N,
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) =
      ∑ x : ZMod N,
        ((k : ℝ) ^ (2 * m) *
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m)) := by
      rw [Finset.mul_sum]
    _ = ∑ x : ZMod N,
        |sampleDeviation A f (a - fun _ ↦ t) x -
          sampleDeviation A f a (x + t)| ^ (2 * m) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← mul_pow]
      have hkabs : |(k : ℝ)| = k := abs_of_nonneg (Nat.cast_nonneg k)
      rw [← hkabs, ← abs_mul, ← sampleDeviation_sub_const_identity]
    _ ≤ ∑ x : ZMod N, 2 ^ (2 * m - 1) *
        (|sampleDeviation A f (a - fun _ ↦ t) x| ^ (2 * m) +
          |sampleDeviation A f a (x + t)| ^ (2 * m)) := by
      refine Finset.sum_le_sum fun x _ ↦ ?_
      calc
        |sampleDeviation A f (a - fun _ ↦ t) x -
            sampleDeviation A f a (x + t)| ^ (2 * m) ≤
          (|sampleDeviation A f (a - fun _ ↦ t) x| +
            |sampleDeviation A f a (x + t)|) ^ (2 * m) := by
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_sub _ _)
            _
        _ ≤ _ := add_pow_le (abs_nonneg _) (abs_nonneg _) _
    _ = 2 ^ (2 * m - 1) *
        ((∑ x : ZMod N,
            |sampleDeviation A f (a - fun _ ↦ t) x| ^ (2 * m)) +
          ∑ x : ZMod N, |sampleDeviation A f a (x + t)| ^ (2 * m)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 ^ (2 * m - 1) * (C + C) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hatMoment (by rwa [hshift])
      · positivity
    _ = 2 ^ (2 * m) * C := by
      conv_rhs => rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_add, pow_one]
      ring

end CyclicCrootSisask
end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open Finset
open scoped BigOperators Pointwise

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

theorem exists_local_shift_fiber {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty) {k : ℕ}
    (L : Finset (Fin k → G)) (hL : L.Nonempty) (hLA : L ⊆ A ^^ k) :
    ∃ (x : Fin k → G) (T : Finset G), T ⊆ S ∧ T.Nonempty ∧
      ((L.card : ℝ) * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card ∧
      ∀ t ∈ T, (x - fun _ => t) ∈ L := by
  classical
  let P := L ×ˢ S
  let X := (A + S) ^^ k
  let φ : ((Fin k → G) × G) → (Fin k → G) := fun z => z.1 + fun _ => z.2
  have hX : X.Nonempty := (hA.add hS).piFinset_const
  have hmap : ∀ z ∈ P, φ z ∈ X := by
    rintro ⟨a, t⟩ hat
    obtain ⟨ha, ht⟩ := Finset.mem_product.mp hat
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.add_mem_add (Fintype.mem_piFinset.mp (hLA ha) i) ht
  have hXcard : (X.card : ℝ) = ((A + S).card : ℝ) ^ k := by
    simp [X]
  have hXne : (X.card : ℝ) ≠ 0 := by exact_mod_cast hX.card_ne_zero
  have hpigeon : ∃ x ∈ X, ((L.card : ℝ) * S.card) / X.card ≤
      ∑ z ∈ P with φ z = x, (1 : ℝ) := by
    apply Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap hX
    simp only [nsmul_eq_mul, sum_const, P, card_product, Nat.cast_mul]
    rw [mul_comm (X.card : ℝ), div_mul_cancel₀ _ hXne, mul_one]
  obtain ⟨x, _hx, hx⟩ := hpigeon
  let Q := P.filter (fun z => φ z = x)
  let T := Q.image Prod.snd
  have hQcard : (Q.card : ℝ) = ∑ z ∈ P with φ z = x, (1 : ℝ) := by simp [Q]
  have hinj : _root_.Set.InjOn Prod.snd (Q : _root_.Set ((Fin k → G) × G)) := by
    rintro ⟨a, s⟩ has ⟨b, t⟩ hbt hst
    have hab : a + (fun _ => s) = b + fun _ => t :=
      (Finset.mem_filter.mp has).2.trans (Finset.mem_filter.mp hbt).2.symm
    cases hst
    apply Prod.ext
    · funext i
      exact add_right_cancel (congrFun hab i)
    · rfl
  have hTcard : T.card = Q.card := Finset.card_image_iff.mpr hinj
  have hQpos : (0 : ℝ) < Q.card := by
    have hratio : 0 < ((L.card : ℝ) * S.card) / X.card := by
      apply div_pos
      · exact mul_pos (by exact_mod_cast hL.card_pos) (by exact_mod_cast hS.card_pos)
      · exact_mod_cast hX.card_pos
    exact hratio.trans_le (by simpa only [← hQcard] using hx)
  have hT : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    exact_mod_cast hQpos
  refine ⟨x, T, ?_, hT, ?_, ?_⟩
  · intro t ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2
  · rw [← hXcard, hTcard, hQcard]
    exact hx
  · intro t ht
    obtain ⟨⟨a, s⟩, has, hst⟩ := Finset.mem_image.mp ht
    have hax := (Finset.mem_filter.mp has).2
    have ha := (Finset.mem_product.mp (Finset.mem_filter.mp has).1).1
    have heq : (x - fun _ => t) = a := by
      funext i
      have h := congrFun hax i
      change a i + s = x i at h
      change s = t at hst
      simp only [Pi.sub_apply]
      rw [← h, hst, add_sub_cancel_right]
    rw [heq]
    exact ha

end Erdos3.CyclicCrootSisask

end

end OAI
