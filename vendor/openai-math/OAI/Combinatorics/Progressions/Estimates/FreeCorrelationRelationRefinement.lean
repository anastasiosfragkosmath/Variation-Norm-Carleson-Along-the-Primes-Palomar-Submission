/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FreeCorrelationRelationRefinement.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Linear.FourBalancedDual
public import OAI.Combinatorics.Progressions.Linear.NativeSharedFreeRankRelation
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

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

noncomputable def realCoefficientFourSpace (d : Fin (s + 1)) :
    Submodule ℝ (Fin 4 → ℝ ⊗[ℚ] W.L) :=
  ((D.coefficientFourSpace d).baseChange ℝ).map
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)).toLinearMap

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

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

theorem mem_real_coefficientFourSpace (d : Fin (s + 1))
    (v : (W.rank.filtration.fourHorizontalLayer d.val).baseChange ℝ) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) v.val ∈
        D.realCoefficientFourSpace d ↔
      W.rank.filtration.realFourHorizontalMap d.val v ∈ (D.horizontal d).baseChange ℝ := by
  obtain ⟨x, rfl⟩ :=
    (realificationSubmoduleEquiv (W.rank.filtration.fourHorizontalLayer d.val)).surjective v
  rw [W.rank.filtration.realFourHorizontalMap_baseChange]
  unfold realCoefficientFourSpace
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    realificationSubmoduleEquiv_coe, coefficientFourSpace, realification_map, realification_comap]
  constructor
  · rintro ⟨y, hy, he⟩
    have h := realification_subtype_injective (W.rank.filtration.fourHorizontalLayer d.val) he
    exact h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

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
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.finite_combined_free_sunflower {J : Type*} [Fintype J]
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (v : J → D.CoefficientFreeLieAlgebra) (hv : ∀ i, v i ∈ D.coefficientFreeSpan (d i))
    (i j : J) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : v i ∈ D.dependentFreeSpan (d i)) (hvj : v j ∈ D.dependentFreeSpan (d j)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  classical
  let e := Fintype.equivFin J
  have hweight : lieTreeWeight (fun k => (d (e.symm k)).val + 1) (FreeMagma.map e a) = s := by
    rw [lieTreeWeight_relabel]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hd
  have hsupp (k : J) (hk : k ∈ lieTreeSupport a) : e k ∈ lieTreeSupport (FreeMagma.map e a) := by
    rw [lieTreeSupport_relabel]
    exact ⟨k, hk, rfl⟩
  have h := B.combined_free_sunflower D (Fintype.card J) (fun k => d (e.symm k))
    (FreeMagma.map e a) hweight ((lieTreeLength_relabel e a).trans hr)
    (fun k => v (e.symm k)) (fun k => hv (e.symm k)) (e i) (e j)
    (fun h => hij (e.injective h)) (hsupp i hi) (hsupp j hj)
    (by simpa only [Equiv.symm_apply_apply] using hvi)
    (by simpa only [Equiv.symm_apply_apply] using hvj)
  simpa only [lieTreeEval_relabel, Function.comp_def, Equiv.symm_apply_apply] using h

theorem CoefficientBases.exists_free_tree_linearization {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (x : J → D.CoefficientFreeLieAlgebra) (hx : ∀ i, x i ∈ D.coefficientFreeSpan (d i)) :
    ∃ A : (∀ i, D.dependentFreeSpan (d i)) →ₗ[ℚ] ℚ, ∀ y : ∀ i, D.dependentFreeSpan (d i),
      B.freeFrequency D (lieTreeEval (fun i => x i + (y i : D.CoefficientFreeLieAlgebra)) a) =
        B.freeFrequency D (lieTreeEval x a) + A y := by
  apply exists_linear_lieTree_expansion (B.freeFrequency D)
    (fun i => D.coefficientFreeSpan (d i)) (fun i => D.dependentFreeSpan (d i))
    (fun i => D.dependentFreeSpan_le_coefficientFreeSpan (d i)) a x hx
  intro v hv i j hij hi hj
  exact B.finite_combined_free_sunflower D (fun k => d (lieTreeOccurrenceLabel a k))
    (lieTreeOccurrenceTree a)
    ((lieTreeOccurrenceTree_weight (fun k => (d k).val + 1) a).trans hd)
    ((lieTreeOccurrenceTree_length a).trans hr) v hv i j hij
    (by rw [lieTreeOccurrenceTree_support]; trivial)
    (by rw [lieTreeOccurrenceTree_support]; trivial) hi hj

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

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
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.free_refined_four_identity {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (K : J → Submodule ℚ (Fin 4 → D.CoefficientFreeLieAlgebra))
    (hK : ∀ v, (∀ i, v i ∈ K i) →
      fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0)
    (v : J → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (K i)) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 :=
  four_refined_affine_identity _ _ _
    (fun x hx => B.exists_free_tree_linearization D d a hd hr x hx) K hK v hv

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.correlation_four_frequency
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 := by
  have h := D'.coefficient_four_frequency n (fun i => ⟨(d i).val + 1, by omega⟩)
    a hd hr v hv
  change fourFunctionDifference (fun x => V.frequency (lieTreeEval x a)) v = 0 at h
  simpa only [hfreq] using h

theorem CoefficientBases.correlation_refined_four_identity
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 :=
  B.free_refined_four_identity D d a hd hr _
    (B.correlation_four_frequency D E T hbQ hT V g hg D' hfreq n d a hd hr) v hv

end Erdos3.NativeRankRelation.CommonData

end

end OAI
