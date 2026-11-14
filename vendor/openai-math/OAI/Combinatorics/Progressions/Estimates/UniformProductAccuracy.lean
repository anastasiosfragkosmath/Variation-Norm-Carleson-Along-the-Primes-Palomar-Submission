/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/UniformProductAccuracy.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem abs_finset_prod_sub_prod_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ S, |f i| ≤ B) (hg : ∀ i ∈ S, |g i| ≤ B)
    (hdiff : ∀ i ∈ S, |f i - g i| ≤ δ) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ S.card * δ * B ^ S.card := by
  classical
  revert hf hg hdiff
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert a S ha ih =>
    intro hf hg hdiff
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hdS := fun i hi => hdiff i (Finset.mem_insert_of_mem hi)
    have hrec := ih hfS hgS hdS
    have hprod : |∏ i ∈ S, g i| ≤ B ^ S.card := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _i ∈ S, B := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hgS
        _ = _ := by simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) + (f a - g a) * ∏ i ∈ S, g i| := by
        congr 1
        ring
      _ ≤ |f a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| + |f a - g a| * |∏ i ∈ S, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ B * (S.card * δ * B ^ S.card) + δ * B ^ S.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (abs_nonneg _) (by linarith))
          (mul_le_mul (hdiff a (Finset.mem_insert_self _ _)) hprod (abs_nonneg _) hδ)
      _ = (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ S.card := by rw [pow_succ]; ring
      _ ≤ (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ _)) hδ)
      _ = _ := by push_cast; ring

theorem abs_pow_sub_pow_box_bound {x y B δ : ℝ} {n s : ℕ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hxy : |x - y| ≤ δ) (hn : n ≤ s) :
    |x ^ n - y ^ n| ≤ δ * s * B ^ s := by
  apply (abs_pow_sub_pow_le x y n).trans
  apply mul_le_mul (mul_le_mul hxy (Nat.cast_le.mpr hn) (Nat.cast_nonneg _) hδ)
  · exact (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le hx hy) _).trans
      (pow_le_pow_right₀ hB (by omega))
  · positivity
  · positivity

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI
