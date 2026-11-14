/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/CommonDependentPolynomialIntersections.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def dependentPolynomialLayer (d k l : ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ D.CoefficientFreeLieAlgebra) :=
  markedPolynomialLayer D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent d k l

theorem coefficientFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.coefficientFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 0 1 :=
  sup_le (D.commonFreeSpan_le_dependentWordLayer d)
    ((D.dependentFreeSpan_le_dependentWordLayer d).trans
      (D.dependentWordLayer_antitone le_rfl (Nat.zero_le 1) le_rfl))

variable {Q : ℝ} (B : D.CoefficientBases Q)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

variable {Q : ℝ} (B : D.CoefficientBases Q)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
