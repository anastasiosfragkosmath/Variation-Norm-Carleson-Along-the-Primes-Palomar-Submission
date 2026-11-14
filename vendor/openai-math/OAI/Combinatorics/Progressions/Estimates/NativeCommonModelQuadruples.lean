/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeCommonModelQuadruples.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import OAI.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise

structure NativeCyclicModel (degree N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  norm : test.normBound ≤ 1
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = test.evalCyclic N (fun _ => x)

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

def nativeCyclicFunctions (degree N : ℕ) [NeZero N] (p : ℝ) : Set (ZMod N → ℂ) :=
  {f | Nonempty (NativeCyclicModel degree N p f)}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def CyclicNativeInverse (s C : ℕ) : Prop :=
  ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → ∀ f : ZMod N → ℂ,
    (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 1) f →
    ∃ g ∈ nativeCyclicFunctions s N ((p + C) ^ C),
      Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x, f x * star (g x)‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeCommonDerivativeModels (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  geometry : model.GeometryComplexityLE p
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  test : ZMod N → model.Niltest (fun _ : Unit => 1)
  norm : ∀ h, (test h).normBound ≤ 1
  complexity : ∀ h, (test h).ComplexityLE p
  common_observable : ∀ h k, (test h).observable = (test k).observable
  correlation : ∀ h ∈ shifts, Real.exp (-p) ≤
    ‖𝔼 x, multiplicativeDerivative f h x * star ((test h).evalCyclic N (fun _ => x))‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

noncomputable def NativeCommonDerivativeModels.mono {s N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} (B : NativeCommonDerivativeModels s N p f) (hpq : p ≤ q) :
    NativeCommonDerivativeModels s N q f :=
  { B with
    geometry := B.geometry.mono B.model hpq
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans B.density
    complexity := fun h => (B.complexity h).mono hpq
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (B.correlation h hh) }

theorem exists_normalized_native_common_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ},
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → (B : NativeCommonDerivativeModels s N p f) →
      ∃ R : NativeCommonDerivativeModels s N ((p + C) ^ C) f,
        ∀ h, R.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
          (R.test h).orbit = 1 := by
  obtain ⟨a, _, hnormalize⟩ := RationalFilteredNilmanifold.exists_normalized_common_correlators s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro N _ p f hp hf B
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨H, S, _, hH, hdense, hS, hsame, hcorr⟩ :=
    hnormalize B.model B.test B.shifts B.nonempty hp B.geometry B.complexity
      (fun h _ => B.norm h) (fun h x => multiplicativeDerivative f h x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h x) B.correlation
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (p + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)
      _ = Real.exp (-((p + a) ^ a)) * (Real.exp (-p) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((p + a) ^ a)) * B.shifts.card :=
        mul_le_mul_of_nonneg_left B.density (Real.exp_nonneg _)
      _ ≤ _ := hdense
  let R : NativeCommonDerivativeModels s N ((p + C) ^ C) f := {
    L := B.L
    dim := B.dim
    model := B.model
    geometry := B.geometry.mono B.model hpC
    shifts := H
    nonempty := hH
    density := hfinaldensity
    test := S
    norm := fun h => (hS h).1
    complexity := fun h => (hS h).2.2.1.mono hqC
    common_observable := hsame
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh) }
  exact ⟨R, fun h => (hS h).2.2.2⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem cyclicNativeInverse_one : CyclicNativeInverse 1 2 := by
  intro N _ p hp f hf hG
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_gowers_two f hf
  obtain ⟨T, hTn, hTc, hTeval⟩ := exists_cyclic_character_niltest χ
  have h12 : (12 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have h2p : 2 * p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hcorr : Real.exp (-(2 * p)) ≤ ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ gowersNorm 2 f ^ 2 := pow_le_pow_left₀ (Real.exp_nonneg _) hG 2
      _ ≤ _ := hχ
  let F : NativeCyclicModel 1 N ((p + 2) ^ 2) (fun x => χ x) := {
    L := RationalTorus.Algebra 1
    dim := 1
    model := RationalTorus.nilmanifold 1
    test := T
    norm := hTn
    complexity := hTc.mono h12
    eval := fun x => (hTeval x).symm }
  exact ⟨fun x => χ x, ⟨F⟩, (Real.exp_le_exp.mpr (neg_le_neg h2p)).trans hcorr⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem mean_norm_le_fourier_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) : (𝔼 x, ‖f x‖) ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ := by
  have hpoint (x : G) : ‖f x‖ ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = ‖∑ χ : AddChar G ℂ, finiteFourierCoeff f χ * χ x‖ := by rw [finiteFourier_inversion]
      _ ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ * χ x‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, AddChar.norm_apply, mul_one]
  exact (Finset.expect_le_expect (fun x _ => hpoint x)).trans_eq (Fintype.expect_const _)

theorem exists_quadratic_small_modulus_correlation {N : ℕ} [NeZero N] {p q : ℝ}
    (hN : (N : ℝ) ≤ Real.exp q) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hGowers : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ g ∈ nativeCyclicFunctions 2 N 211,
      Real.exp (-(8 * p + q)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  have hmass : Real.exp (-(8 * p)) ≤ ∑ χ : AddChar (ZMod N) ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ 8 := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ gowersNorm 3 f ^ 8 := pow_le_pow_left₀ (Real.exp_nonneg _) hGowers 8
      _ ≤ 𝔼 n, ‖f n‖ := by simpa using gowersNorm_pow_le_mean_norm 2 f hf
      _ ≤ _ := mean_norm_le_fourier_sum f
  obtain ⟨χ, hχ⟩ := exists_large_nonnegative_weighted_term
    (fun _ : AddChar (ZMod N) ℂ => (1 : ℝ)) (fun χ => ‖finiteFourierCoeff f χ‖)
    (fun _ => by norm_num) (fun _ => norm_nonneg _) (Real.exp_pos _) (Real.exp_pos q)
    (by simpa using hN) (by simpa only [one_mul] using hmass)
  have hcorr : Real.exp (-(8 * p + q)) ≤ ‖finiteFourierCoeff f χ‖ := by
    have heq : Real.exp (-(8 * p)) / Real.exp q = Real.exp (-(8 * p + q)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hχ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := exists_cyclic_character_niltest χ
  let hdegree : 1 ≤ 2 := by omega
  refine ⟨fun n => χ n, ⟨{
    L := RationalTorus.Algebra 1
    dim := 1
    model := (RationalTorus.nilmanifold 1).raiseStep hdegree
    test := T.raiseStep hdegree
    norm := hTnorm
    complexity := ?_
    eval := ?_ }⟩, hcorr⟩
  · have hh := T.raiseStep_complexity hdegree (by norm_num) hT
    convert hh using 1
    norm_num [raisedNiltestBudget]
  · intro n
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    exact (hTeval n).symm

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeVerticalDerivativeData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) where
  normalized : ∀ h, B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
    (B.test h).orbit = 1
  frequency : B.L →ₗ[ℚ] ℚ
  height : ∀ i, rationalLogHeight (frequency (B.model.basis i)) ≤ p
  vertical : ∀ h z, z ∈ B.model.filtration.realification.subgroup s → ∀ x,
    (B.test h).observable (z • x) =
      CircleFourier.character ((realifyFunctional frequency z.coord : ℝ) : CircleFourier.Circle) *
        (B.test h).observable x
  integral : ∀ z : B.model.RealGroup, z ∈ B.model.filtration.realification.subgroup s →
    z ∈ B.model.realLattice → ∃ n : ℤ, realifyFunctional frequency z.coord = n

noncomputable def NativeVerticalDerivativeData.mono {s N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {B : NativeCommonDerivativeModels s N p f}
    (V : NativeVerticalDerivativeData B) (hpq : p ≤ q) :
    NativeVerticalDerivativeData (B.mono hpq) where
  normalized := V.normalized
  frequency := V.frequency
  height i := (V.height i).trans hpq
  vertical := V.vertical
  integral := V.integral

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

end Erdos3

end

end OAI
