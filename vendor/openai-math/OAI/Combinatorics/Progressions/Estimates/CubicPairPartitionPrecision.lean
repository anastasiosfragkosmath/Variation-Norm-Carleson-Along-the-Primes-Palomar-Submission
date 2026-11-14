/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CubicPairPartitionPrecision.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CubicPairFactoredModel
@[expose] public section

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

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
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

noncomputable def cubicPairAnchoredVector (y : Fin 3 → ℤ)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin 3 → ℤ) : ℂ :=
  R.cubicPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

end Erdos3.NativePolynomialOrbitFactors

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors.FrozenMiddleRealization

variable {p q r b : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}
  [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.cubicPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

end NativePolynomialOrbitFactors.FrozenMiddleRealization

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

theorem norm_sub_positive_sum_le_weighted {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (t : ℂ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ‖t - ∑ i, (w i : ℂ) * c i‖ ≤ ∑ i, w i * ‖t - c i‖ := by
  have hsumC : (∑ i, (w i : ℂ)) = 1 := by exact_mod_cast hsum
  have hid : t - ∑ i, (w i : ℂ) * c i = ∑ i, (w i : ℂ) * (t - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumC, one_mul]
  rw [hid]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]

theorem weighted_partition_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w : I → X → ℝ) (c : I → X → ℂ) (T : X → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x, ∑ i, w i x = 1) (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (hT : ∀ x, ‖T x‖ ≤ 1)
    (hgood : ∀ i x, x ∉ E → 0 < w i x → ‖T x - c i x‖ ≤ ε) :
    (𝔼 x, ∑ i, w i x * ‖T x - c i x‖) ≤ ε + 2 * (E.card : ℝ) / Fintype.card X := by
  have hn (x : X) : 0 ≤ ∑ i, w i x * ‖T x - c i x‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i x) (norm_nonneg _))
  have hb (x : X) (d : ℝ) (h : ∀ i, 0 < w i x → ‖T x - c i x‖ ≤ d) :
      (∑ i, w i x * ‖T x - c i x‖) ≤ d := by
    calc
      _ ≤ ∑ i, w i x * d := by
        apply Finset.sum_le_sum
        intro i _
        rcases (hw i x).eq_or_lt with hi | hi
        · rw [← hi, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h i hi) (hw i x)
      _ = d := by rw [← Finset.sum_mul, hsum, one_mul]
  have ha (x : X) : |∑ i, w i x * ‖T x - c i x‖| = ∑ i, w i x * ‖T x - c i x‖ :=
    abs_of_nonneg (hn x)
  have herr := expect_abs_le_of_exceptional_set E
    (fun x => ∑ i, w i x * ‖T x - c i x‖) hε
    (fun x => by
      rw [ha]
      exact hb x 2 (fun i _ => (norm_sub_le _ _).trans (by linarith [hT x, hc i x])))
    (fun x hx => by rw [ha]; exact hb x ε (fun i hi => hgood i x hx hi))
  simpa only [ha] using herr

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

end NativePolynomialOrbitFactors

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

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}

structure NativeCubicPairPartition
    (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
      V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
      (fun _ : Fin 3 => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin 3 → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin 3 → I) → (Fin 3 → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence 2 b
    (R.cubicPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.cubicPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  weighted_approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin 3 → ZMod N,
      ∑ j, (∏ l, weight (j l) (x l) : ℝ) * ‖W.eval out
        (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ) (((x 0).val : ℤ) + shift)) -
          R.cubicPairAnchoredVector (fun l => ((anchor j l).val : ℤ)) k out
            (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativeCubicPairPartition.finite

end Data

end Erdos3

end

end OAI
