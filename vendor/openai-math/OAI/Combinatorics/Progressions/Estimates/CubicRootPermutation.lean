/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CubicRootPermutation.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
public import OAI.Combinatorics.Progressions.Polynomial.PositiveDegreeCyclicDifference
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicPairComponent (out : Fin W.outputDim × Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) : W.model.Niltest (fun _ : Fin 3 => 1) :=
  ((W.tensorPower 2).component ((tensorIndexEquiv W.outputDim 2) ![out.1, out.2])).affinePullback
    (fun j l => if l = (if j.1 = 0 then h else if j.2.val = 0 then y else k) then 1 else 0)
    (fun j => if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicOriginalComponent (out : Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) : W.model.Niltest (fun _ : Fin 3 => 1) :=
  (W.component out).affinePullback
    (fun j l => if l = (if j.1 = 0 then h else if j.2.val = 0 then y else k) then 1 else 0)
    (fun j => if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift)

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
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

abbrev CubicPairAlgebra := ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

noncomputable def cubicPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ _ : CubicReplicatedIndex, 1) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by decide)) (fun _ : Fin 2 => W.model)

noncomputable def cubicPairTests :
    ∀ k, (V.cubicPairModels k).Niltest (fun _ : Fin 3 => 1)
  | none => (V.test.raiseStep (by decide)).conjugate
  | some k => ![(W.cubicPairComponent i 1 2 0 shift).conjugate,
      W.cubicPairComponent j 2 1 0 shift] k

noncomputable def cubicPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![-(2 • W.vertical.frequency), 2 • W.vertical.frequency] k

end NativeSampleCorrelation
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
