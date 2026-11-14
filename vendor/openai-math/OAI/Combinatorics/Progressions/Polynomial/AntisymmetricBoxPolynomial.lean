/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/AntisymmetricBoxPolynomial.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def antisymmetricBoxPolynomial (i j : Fin W.outputDim) :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun _ : Fin 8 => W.model.filtration)
    (fun k => (W.antisymmetricBoxFactors i j k).orbit)
  ⟨⟨o.log, o.property⟩⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
