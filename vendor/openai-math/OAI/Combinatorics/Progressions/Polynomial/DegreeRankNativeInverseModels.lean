/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/DegreeRankNativeInverseModels.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeDegreeRankDerivativeData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) (r : ℕ) (q : ℝ) where
  vertical : NativeVerticalDerivativeData B
  unit : NativeUnitVerticalData B vertical q
  rank : B.model.DegreeRankStructure r
  complexity : rank.ComplexityLE q

namespace NativeDegreeRankDerivativeData

variable {s N r : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def mono {p' q' : ℝ} (hp : p ≤ p') (hq : q ≤ q') :
    NativeDegreeRankDerivativeData (B.mono hp) r q' where
  vertical := W.vertical.mono hp
  unit := W.unit.mono hp hq
  rank := W.rank
  complexity := W.complexity.mono W.rank hq

theorem rank_vertical (i : Fin (W.unit.tailDim + 1)) (z : B.model.RealGroup)
    (hz : z ∈ W.rank.realSubgroup s r) (x : B.model.Space) :
    W.unit.observable i (z • x) =
      CircleFourier.character ((realifyFunctional W.vertical.frequency z.coord : ℝ) :
        CircleFourier.Circle) * W.unit.observable i x :=
  W.unit.vertical i z (W.rank.realSubgroup_le_degree s r hz) x

theorem rank_integral (z : B.model.RealGroup) (hz : z ∈ W.rank.realSubgroup s r)
    (hΓ : z ∈ B.model.realLattice) : ∃ n : ℤ, realifyFunctional W.vertical.frequency z.coord = n :=
  W.vertical.integral z (W.rank.realSubgroup_le_degree s r hz) hΓ

end NativeDegreeRankDerivativeData

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_degree_rank_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ B : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        Nonempty (NativeDegreeRankDerivativeData B s ((p + D) ^ D)) := by
  obtain ⟨a, _, hmodels⟩ := exists_unit_vertical_native_inverse_models hI
  obtain ⟨b, _, hrank⟩ := RationalFilteredNilmanifold.exists_native_degree_rank_structure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have ht : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hcost : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqD : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  have htD : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by linarith
  obtain ⟨B, V, ⟨U⟩⟩ := hmodels hp f hf hG
  obtain ⟨R, _, hR⟩ := hrank B.model hq B.geometry
  refine ⟨B.mono hqD, ⟨{
    vertical := V.mono hqD
    unit := U.mono hqD hqD
    rank := R
    complexity := hR.mono R htD
  }⟩⟩

end Erdos3

end

end OAI
