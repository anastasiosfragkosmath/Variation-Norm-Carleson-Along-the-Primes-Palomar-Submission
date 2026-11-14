/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeEquivalenceTransitivity.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
public import OAI.Combinatorics.Progressions.Nilpotent.NativeNilsequenceExpansion
@[expose] public section

namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

def BoolLieFamily (L₁ L₂ : Type u) : Bool → Type u
  | false => L₂
  | true => L₁

namespace BoolLieFamily

variable {L₁ L₂ : Type u} [LieRing L₁] [LieAlgebra ℚ L₁]
    [LieRing L₂] [LieAlgebra ℚ L₂]

instance instLieRing (b : Bool) : LieRing (BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : LieRing L₂)
  · exact (inferInstance : LieRing L₁)

instance instLieAlgebra (b : Bool) : LieAlgebra ℚ (BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : LieAlgebra ℚ L₂)
  · exact (inferInstance : LieAlgebra ℚ L₁)

variable [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₂)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂)] [T2Space (ℝ ⊗[ℚ] L₂)]

instance instTopologicalSpace (b : Bool) :
    TopologicalSpace (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₁))

instance instIsTopologicalAddGroup (b : Bool) :
    IsTopologicalAddGroup (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁))

instance instContinuousSMul (b : Bool) :
    ContinuousSMul ℝ (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁))

instance instT2Space (b : Bool) : T2Space (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₁))

end BoolLieFamily
end Erdos3

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeVectorEquivalence

variable {J K : Type*} [Fintype J] [Fintype K] {s N : ℕ} [NeZero N] {p q : ℝ}
  {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ}

end Erdos3.NativeVectorEquivalence

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeVectorEquivalence

open scoped BigOperators

end Erdos3.NativeVectorEquivalence

end

end OAI
