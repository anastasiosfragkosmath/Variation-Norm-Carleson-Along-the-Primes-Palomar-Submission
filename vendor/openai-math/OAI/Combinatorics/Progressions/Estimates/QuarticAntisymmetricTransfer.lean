/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/QuarticAntisymmetricTransfer.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.QuarticSurvivorMultilinearization
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def quarticReflectionSource {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (c : ℤ) (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 4 → ℤ) : ℂ :=
  W.eval a.1 (quarticInput (x 0) ![c - x 0 - x 1, x 2, x 3]) *
    star (W.eval a.2 (quarticInput (x 1) ![c - x 0 - x 1, x 2, x 3]))

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def NativeMultidegreeNilcharacter.quarticAntisymmetric {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (i j : Fin W.outputDim) (x : Fin 4 → ℤ) : ℂ :=
  W.eval i (quarticInput (x 0) ![x 1, x 2, x 3]) *
    star (W.eval j (quarticInput (x 1) ![x 0, x 2, x 3]))

end Erdos3

end

end OAI
