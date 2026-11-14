/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Fourier/CommonDependentWordFrequency.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
public import OAI.Combinatorics.Progressions.Estimates.FreeCorrelationRelationRefinement
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
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.dependent_word_frequency_zero (a : FreeMagma D.CoefficientAlphabet)
    (hd : lieTreeWeight D.coefficientWeight a = s) (hr : a.length = r)
    (ha : 2 ≤ lieTreeMarkedCount D.coefficientIsDependent a) :
    B.freeFrequency D (lieTreeEval D.coefficientFreeGenerator a) = 0 := by
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_marked_occurrences D.coefficientIsDependent a ha
  have hweight :
      lieTreeWeight (fun k => (D.coefficientLayerIndex (lieTreeOccurrenceLabel a k)).val + 1)
        (lieTreeOccurrenceTree a) = s := by
    simp only [← D.coefficientWeight_eq_layerIndex]
    exact (lieTreeOccurrenceTree_weight D.coefficientWeight a).trans hd
  have h := B.finite_combined_free_sunflower D
    (fun k => D.coefficientLayerIndex (lieTreeOccurrenceLabel a k))
    (lieTreeOccurrenceTree a) hweight ((lieTreeOccurrenceTree_length a).trans hr)
    (D.coefficientFreeGenerator ∘ lieTreeOccurrenceLabel a)
    (fun k => D.coefficientFreeGenerator_mem_combined (lieTreeOccurrenceLabel a k))
    i j hij (by rw [lieTreeOccurrenceTree_support]; trivial)
    (by rw [lieTreeOccurrenceTree_support]; trivial)
    (D.coefficientFreeGenerator_mem_dependent _ hi)
    (D.coefficientFreeGenerator_mem_dependent _ hj)
  rwa [lieTreeOccurrenceTree_eval] at h

theorem CoefficientBases.dependentWordLayer_top_le_ker :
    D.dependentWordLayer s 2 r ≤ (B.freeFrequency D).ker :=
  markedLieSpan_top_le_ker D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientFreeGenerator_mem_layer
    2 (B.freeFrequency D) (B.dependent_word_frequency_zero D)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
