/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/QuarticPairFactors.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.MixedAnchorExpansion
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticPairComponent (out : Fin W.outputDim) (v : Fin 4 → Fin 4) :
    W.model.Niltest (fun _ : Fin 4 => 1) :=
  (W.component out).affinePullback
    (fun j a => if a = (if j.1 = 0 then v 0 else if j.2.val = 0 then v 1
      else if j.2.val = 1 then v 2 else v 3) then 1 else 0) (fun _ => 0)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ))))

abbrev QuarticPairAlgebra := ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

noncomputable def quarticPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ _ : QuarticReplicatedIndex, 1) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by decide)) (fun _ : Fin 2 => W.model)

noncomputable def quarticPairTests :
    ∀ k, (V.quarticPairModels k).Niltest (fun _ : Fin 4 => 1)
  | none => (V.test.raiseStep (by decide)).conjugate
  | some k => ![W.quarticPairComponent i id,
      (W.quarticPairComponent j ![1, 0, 2, 3]).conjugate] k

noncomputable def quarticPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

end NativeSampleCorrelation
end Erdos3

end

end OAI
