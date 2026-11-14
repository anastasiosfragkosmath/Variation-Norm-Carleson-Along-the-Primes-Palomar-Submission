/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ProperSubspaceCount.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Pi
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι]

theorem exists_coordinate_injective_of_ne_top
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤) :
    ∃ j : ι, ∀ x ∈ U, ∀ y ∈ U, (∀ i, i ≠ j → x i = y i) → x = y := by
  classical
  obtain ⟨f, hf, hzero⟩ := U.exists_dual_map_eq_bot_of_lt_top hU.lt_top inferInstance
  have hfzero : ∀ x ∈ U, f x = 0 := by
    intro x hx
    have hm : f x ∈ U.map f := ⟨x, hx, rfl⟩
    simpa only [hzero, Submodule.mem_bot] using hm
  have hcoord : ∃ j : ι, f (fun i => if j = i then 1 else 0) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [h, smul_zero, Finset.sum_const_zero]
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨j, ?_⟩
  intro x hx y hy hxy
  have he : f (x - y) = (x j - y j) * f (fun i => if j = i then 1 else 0) := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    apply Finset.sum_eq_single j
    · intro i _ hij
      simp only [Pi.sub_apply, hxy i hij, sub_self, zero_smul]
    · simp
  have hjxy : x j = y j := by
    rw [map_sub, hfzero x hx, hfzero y hy, sub_self] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hj)
  funext i
  by_cases hij : i = j
  · simpa only [hij] using hjxy
  · exact hxy i hij

theorem integer_points_card_le_of_proper_subspace [DecidableEq ι]
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤)
    (H : Finset (ι → ℤ)) (S : ι → Finset ℤ)
    (hmem : ∀ h ∈ H, (fun i => (h i : ℝ)) ∈ U)
    (hbound : ∀ h ∈ H, ∀ i, h i ∈ S i) :
    ∃ j : ι, H.card ≤ ∏ i : {i : ι // i ≠ j}, (S i.val).card := by
  classical
  obtain ⟨j, hj⟩ := exists_coordinate_injective_of_ne_top U hU
  refine ⟨j, ?_⟩
  let restrict : (ι → ℤ) → ({i : ι // i ≠ j} → ℤ) := fun h i => h i.val
  have hcard : H.card ≤ (Fintype.piFinset (fun i : {i : ι // i ≠ j} => S i.val)).card := by
    apply Finset.card_le_card_of_injOn restrict
    · intro h hh
      exact Fintype.mem_piFinset.mpr (fun i => hbound h hh i.val)
    · intro h hh k hk heq
      have he : (fun i => (h i : ℝ)) = (fun i => (k i : ℝ)) := by
        apply hj _ (hmem h hh) _ (hmem k hk)
        intro i hi
        exact_mod_cast congrFun heq ⟨i, hi⟩
      funext i
      exact_mod_cast congrFun he i
  simpa only [Fintype.card_piFinset] using hcard

end Erdos3

end

end OAI
