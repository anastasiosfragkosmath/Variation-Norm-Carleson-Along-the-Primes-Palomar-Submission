/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/MixedPairPartitionKernel.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.MixedPairPartitionPrecision
public import OAI.Combinatorics.Progressions.Estimates.QuarticPairPartitionPrecision
@[expose] public section

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}

namespace NativeCubicPairPartition

attribute [local instance] NativeCubicPairPartition.finite

variable {b ε : ℝ}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}
  (P : NativeCubicPairPartition R b ε)

end NativeCubicPairPartition
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

end NativeMultidegreeNilcharacter

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}

namespace NativeQuarticPairPartition

attribute [local instance] NativeQuarticPairPartition.finite

variable {b ε : ℝ}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}
  (P : NativeQuarticPairPartition R b ε)

end NativeQuarticPairPartition
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

namespace NativeMixedPairPartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b ε : ℝ}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}
  (P : NativeMixedPairPartition R b ε)

noncomputable def cellWeight (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : ℝ :=
  ∏ l, P.weight (a l) (x l)

theorem cellWeight_nonneg (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : 0 ≤ P.cellWeight a x :=
  Finset.prod_nonneg (fun l _ => ((P.positive (a l)).unit_interval (x l)).1)

theorem cellWeight_total (x : Fin (n + 2) → ZMod N) : ∑ a, P.cellWeight a x = 1 :=
  sum_productPartitionWeight (fun _ : Fin (n + 2) => P.weight) (fun _ => P.total) x

noncomputable def cellVector (a : Fin (n + 2) → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ZMod N) : ℂ :=
  R.mixedPairAnchoredVector (fun l => ((P.anchor a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))

theorem cellVector_norm (a : Fin (n + 2) → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ZMod N) : ‖P.cellVector a k out x‖ ≤ 1 :=
  R.mixedPairAnchoredVector_norm _ _ _ _

end NativeMixedPairPartition
end Erdos3

end

end OAI
