/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/QuadraticCyclicIntegration.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_diagonal_niltest {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (i : Fin W.outputDim) :
    ∃ T : W.model.Niltest (fun _ : Unit => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ n : ℤ, T.eval (fun _ => n) = W.eval i (fun _ => n) := by
  obtain ⟨T, hT, hcomplexity, heval⟩ := W.exists_linear_niltest i
    (fun _ => { toFun := fun x : Unit → ℤ => x (), map_zero' := rfl, map_add' := fun _ _ => rfl })
  exact ⟨T, hT, hcomplexity, fun n => heval (fun _ => n)⟩

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
