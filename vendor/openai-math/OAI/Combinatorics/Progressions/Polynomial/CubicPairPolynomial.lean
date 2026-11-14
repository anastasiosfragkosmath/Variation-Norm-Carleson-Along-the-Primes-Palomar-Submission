/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/CubicPairPolynomial.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CubicRootPermutation
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

noncomputable def cubicPairPolynomial :
    ((pi V.cubicPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 3 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.cubicPairModels k).filtration)
    (fun k => (V.cubicPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

end Erdos3.NativeSampleCorrelation

end

end OAI
