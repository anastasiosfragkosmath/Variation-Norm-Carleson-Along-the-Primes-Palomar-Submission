/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/RealFiniteZeroExtension.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def zeroExtendFinset {X : Type*} (S : Finset X) (f : X → ℂ) (x : X) : ℂ := by
  classical
  exact if x ∈ S then f x else 0

theorem expect_finset_subtype {X : Type*} (S : Finset X) (f : X → ℂ) :
    (𝔼 x : S, f x.val) = 𝔼 x ∈ S, f x := by
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
    Finset.sum_coe_sort]

theorem expect_zeroExtendFinset {X : Type*} (A S : Finset X) (hSA : S ⊆ A) (f : X → ℂ) :
    (𝔼 x ∈ A, zeroExtendFinset S f x) =
      ((S.card : ℂ) / (A.card : ℂ)) * (𝔼 x ∈ S, f x) := by
  classical
  rw [Finset.expect_eq_sum_div_card]
  simp only [zeroExtendFinset, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSA]
  rw [← Finset.card_mul_expect S f]
  ring

theorem norm_expect_zeroExtendFinset {X : Type*} (A S : Finset X) (hSA : S ⊆ A) (f : X → ℂ) :
    ‖𝔼 x ∈ A, zeroExtendFinset S f x‖ =
      ((S.card : ℝ) / (A.card : ℝ)) * ‖𝔼 x ∈ S, f x‖ := by
  rw [expect_zeroExtendFinset A S hSA f, norm_mul, norm_div,
    Complex.norm_natCast, Complex.norm_natCast]

theorem zeroExtendFinset_mul_left {X : Type*} (S : Finset X) (f g : X → ℂ) (x : X) :
    f x * zeroExtendFinset S g x = zeroExtendFinset S (fun x => f x * g x) x := by
  classical
  by_cases hx : x ∈ S <;> simp [zeroExtendFinset, hx]

theorem zeroExtendFinset_mul_star {X : Type*} [DecidableEq X] (S T : Finset X) (f g : X → ℂ) (x : X) :
    zeroExtendFinset S f x * star (zeroExtendFinset T g x) =
      zeroExtendFinset (S ∩ T) (fun x => f x * star (g x)) x := by
  classical
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp [zeroExtendFinset, hs, ht]

theorem zeroExtendFinset_norm_le_one {X : Type*} (S : Finset X) (f : X → ℂ)
    (hf : ∀ x ∈ S, ‖f x‖ ≤ 1) (x : X) : ‖zeroExtendFinset S f x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ S
  · simpa [zeroExtendFinset, hx] using hf x hx
  · simp [zeroExtendFinset, hx]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

end OAI
