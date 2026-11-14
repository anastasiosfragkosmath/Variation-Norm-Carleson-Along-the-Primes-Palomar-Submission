/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/MixedPairPartitionPrecision.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CubicPairPartitionPrecision
public import OAI.Combinatorics.Progressions.Geometry.MixedPairCoordinateTest
@[expose] public section

namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

noncomputable def mixedPairAnchoredVector (y : Fin (n + 2) → ℤ)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x

def HasMixedPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin (n + 2) → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) -
          R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedPairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) :
    W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) =
      R.mixedPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  have hpoly : V.mixedPairPolynomial =
      ⟨⟨(V.mixedPairCoordinateNiltest k out).orbit.log,
        (V.mixedPairCoordinateNiltest k out).orbit.property⟩⟩ := by
    rw [V.mixedPairCoordinateNiltest_orbit]
    exact V.mixedPairPolynomial_eq_test
  calc
    _ = (V.mixedPairCoordinateNiltest k out).eval x :=
      (V.mixedPairCoordinateNiltest_eval k out x).symm
    _ = _ := (R.eval_niltest (V.mixedPairCoordinateNiltest k out) hpoly x).trans
      (V.mixedPairCoordinateNiltest_observable k out _)

theorem mixedPairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin (n + 2) → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.mixedPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.mixedPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.mixedPairModels).basis.baseChange ℝ)
    ‖W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) -
        R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.mixedPairModels
  let T := V.mixedPairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin (n + 2) => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) := by
    have h := T.observable_budget (V.mixedPairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.mixedPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.mixedPairCoordinateNiltest_observable, mixedPairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.mixedPairFrozenVector_diagonal k out x] using hraw

end Erdos3.NativePolynomialOrbitFactors

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_local_approximation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasMixedPairLocalApproximation ((tensorPowerBudget m p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control
    (∑ _ : MixedReplicatedIndex (n + 1), 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r m W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget m p := hW.trans (tensorPowerBudget_bounds m hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := tensorPowerBudget m p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + ((n + 2 : ℕ) : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : tensorPowerBudget m p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have htwo : (Fintype.card (Fin (n + 2)) : ℝ) ≤ t := by
    simp only [Fintype.card_fin]
    dsimp [t]
    linarith
  have hBt : mixedPairBudget (tensorPowerBudget m p) q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget (tensorPowerBudget m p) q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.mixedPairModels).basis
  let D := pi V.mixedPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.mixedPairNiltest_complexity).1.mono D htest
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.mixedPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.mixedPairFrozenVector_error k out x y (hcosets x y hres).1
  have hdist := hmotion x y δ hδ hx hy hnear
  apply herror.trans
  calc
    _ ≤ Real.exp t * (Real.exp ((t + a) ^ a) * δ) :=
      mul_le_mul (Real.exp_le_exp.mpr htest) hdist
        (@dist_nonneg D.RealGroup
          (rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)).toPseudoMetricSpace (R.slowValue x) (R.slowValue y))
        (Real.exp_nonneg t)
    _ = Real.exp (t + (t + a) ^ a) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

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

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem hasMixedPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasMixedPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasMixedPairFrozenEquivalence u b := by
  intro den hm hmb left right hleft hright
  exact (h den hm hmb left right hleft hright).mono hab

def HasMixedPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasMixedPairFrozenEquivalence u b

theorem mixedPairFrozenEquivalence_at {b : ℝ} (h : R.HasMixedPairFrozenReduction b)
    (x : Fin (n + 2) → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence (n + 1) b
      (R.mixedPairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.mixedPairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨den, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv den hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

theorem exists_mixed_pair_frozen_reduction (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasMixedPairFrozenReduction ((tensorPowerBudget m p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_mixed_pair_outer_control n
  obtain ⟨B, _, hfrozen⟩ := exists_mixed_pair_frozen_equivalence n
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r m _ W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget m p := hW.trans (tensorPowerBudget_bounds m hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget m p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (tensorPowerBudget m p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.mixedPairModels).basis
  exact ⟨u, hu, huC, houter (W := W.tensorPower m) (V := V) R hr,
    R.hasMixedPairFrozenEquivalence_mono (hfrozen (W := W) (V := V) R hr hu) hBC⟩

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

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem mixedPairAnchoredVector_norm (y : Fin (n + 2) → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ‖R.mixedPairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

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

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

structure NativeMixedPairPartition
    (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin (n + 2) → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin (n + 2) → I) → (Fin (n + 2) → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence (n + 1) b
    (R.mixedPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.mixedPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  weighted_approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin (n + 2) → ZMod N,
      ∑ j, (∏ l, weight (j l) (x l) : ℝ) * ‖W.eval out
        (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ)
                  (fun j => ((x j.succ.succ).val : ℤ))) -
          R.mixedPairAnchoredVector (fun l => ((anchor j l).val : ℤ)) k out
            (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativeMixedPairPartition.finite

noncomputable def NativeMixedPairPartition.mono
    {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r} {a b ε δ : ℝ}
    (P : NativeMixedPairPartition R a ε) (hab : a ≤ b) (hεδ : ε ≤ δ) : NativeMixedPairPartition R b δ :=
  { P with
    card_bound := P.card_bound.trans (Real.exp_le_exp.mpr hab)
    positive := fun j => (P.positive j).mono le_rfl hab
    equivalence := fun j => (P.equivalence j).mono hab
    weighted_approximation := fun k out => (P.weighted_approximation k out).trans hεδ }

end Data

end Erdos3

end

end OAI
