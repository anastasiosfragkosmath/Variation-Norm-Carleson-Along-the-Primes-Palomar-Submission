/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/MarkedUnitOrbit.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.MultidegreeOrbitTransport
public import OAI.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
@[expose] public section

namespace OAI


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

noncomputable def localAffineMarkedBase (j : Fin s) : (D.coefficientFreeSpan j).baseChange ℝ :=
  ⟨(x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val,
    Submodule.add_mem _ (x j).property (Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.baseChange_mono ℝ
        (D.dependentFreeSpan_le_coefficientFreeSpan j) (y j i).property)))⟩

noncomputable def localAffineMarkedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  D.commonAffineMarkedLift t (D.localAffineMarkedBase t x y u c h₀) y u h.val n

theorem localAffineMarkedLift_eval (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
          (D.localAffineMarkedLift t x y u c h₀ h n) =
            ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
              ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  apply (D.commonAffineMarkedLift_eval t (D.localAffineMarkedBase t x y u c h₀) y u
    (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ)) h.val n).trans
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  change ((x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val) + _ = _
  rw [add_assoc, ← Finset.sum_add_distrib]
  apply congrArg ((x j).val + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_smul]
  apply congrArg (fun a : ℝ => a • (y j i).val)
  simpa only [Int.cast_natCast, add_assoc] using affineCyclicTorusCarry_identity u c h₀ h i

theorem localAffineMarkedLift_eq_polynomial_eval
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (h : ZMod N) (hA : A h = positiveUnivariate (fun j =>
      (x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
          (D.localAffineMarkedLift t x y u c h₀ h n) = eval (fun _ => (n : ℚ)) (A h) := by
  rw [D.localAffineMarkedLift_eval, hA]
  simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

noncomputable def localAffineCorrectingElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  ⟨realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))⟩

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def scaledLocalAffineCorrectingElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  ⟨realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))⟩

end Erdos3.NativeRankRelation.CommonData


namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) {d : ℕ}
  (E : RationalFilteredNilmanifold
    (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
  (T : E.MultidegreeStructure (mixedCorrelationDegree s))
  (hT : T.filtration = D.markedQuotientMultidegree t)

variable [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
  D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]

end Erdos3.NativeRankRelation.CommonData

end OAI
