/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/RealCoefficientKernel.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.FreeCorrelationRelationRefinement
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem coefficientFourSpace_eq_sup (d : Fin (s + 1)) :
    D.coefficientFourSpace d = D.spaces d ⊔
      Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2) := by
  let F := W.rank.filtration
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change F.fourHorizontalMap d.val w ∈ F.horizontalImageOfSubmodule (D.spaces d) d.val at hw
    obtain ⟨z, hz, he⟩ := hw
    apply Submodule.mem_sup.mpr
    refine ⟨z.val, hz, w.val - z.val, ?_, by abel⟩
    apply Submodule.mem_pi.mpr
    intro k _
    exact (F.higherHorizontalMk_eq d.val _ _).mp (congrFun he.symm k)
  · intro hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have hx' := D.spaces_le_fourHorizontalLayer d hx
    have hy' : y ∈ F.fourHorizontalLayer d.val := by
      apply (F.mem_fourHorizontalLayer d.val y).mpr
      intro k
      exact F.lex_antitone (Or.inr ⟨rfl, by omega⟩) ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))
    let z : F.fourHorizontalLayer d.val := ⟨x, hx'⟩
    let w : F.fourHorizontalLayer d.val := ⟨x + y, (F.fourHorizontalLayer d.val).add_mem hx' hy'⟩
    apply (D.mem_coefficientFourSpace d w).mpr
    change F.fourHorizontalMap d.val w ∈ F.horizontalImageOfSubmodule (D.spaces d) d.val
    refine ⟨z, hx, ?_⟩
    funext k
    apply (F.higherHorizontalMk_eq d.val _ _).mpr
    change x k - (x k + y k) ∈ F.layer d.val 2
    simpa only [sub_add_cancel_left] using
      (F.layer d.val 2).neg_mem ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))

theorem fourKernel_le_coefficientFourSpace (d : Fin (s + 1)) :
    Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2) ≤
      D.coefficientFourSpace d := by
  rw [D.coefficientFourSpace_eq_sup]
  exact le_sup_right

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem real_fourKernel_le_coefficientFourSpace (d : Fin (s + 1))
    (v : Fin 4 → ℝ ⊗[ℚ] W.L)
    (hv : ∀ k, v k ∈ (W.rank.filtration.layer d.val 2).baseChange ℝ) :
    v ∈ D.realCoefficientFourSpace d := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  have hbase : e.symm v ∈
      (Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2)).baseChange ℝ := by
    apply (mem_realified_four_product_iff _ _).mpr
    intro k
    change e (e.symm v) k ∈ _
    rw [e.apply_symm_apply]
    exact hv k
  exact ⟨e.symm v, Submodule.baseChange_mono ℝ (D.fourKernel_le_coefficientFourSpace d) hbase,
    e.apply_symm_apply v⟩

theorem realCoefficientFourSpace_congr_mod_kernel (d : Fin (s + 1))
    (v z : Fin 4 → ℝ ⊗[ℚ] W.L)
    (hz : ∀ k, v k - z k ∈ (W.rank.filtration.layer d.val 2).baseChange ℝ) :
    v ∈ D.realCoefficientFourSpace d ↔ z ∈ D.realCoefficientFourSpace d := by
  have h := D.real_fourKernel_le_coefficientFourSpace d (v - z) hz
  constructor
  · intro hv
    simpa only [sub_sub_cancel] using (D.realCoefficientFourSpace d).sub_mem hv h
  · intro hz
    simpa only [sub_add_cancel] using (D.realCoefficientFourSpace d).add_mem h hz

end Erdos3.NativeRankRelation.CommonData

end

end OAI
