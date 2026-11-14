/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/NativeProductOrbitMetric.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.RealProductInclusion
public import OAI.Combinatorics.Progressions.Geometry.CoordinatewiseLipschitz
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def productMetricBound (d : ι → ℕ) : ℝ≥0 :=
  ∑ i, coordinateLipschitzBound (Fintype.card (Σ i, Fin (d i))) (d i) 1

variable {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem productInclusionHom_lipschitz (i : ι) :
    letI := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
      ((D i).basis.baseChange ℝ)
    letI := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi D).basis.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ i, Fin (d i))) (d i) 1)
      (productInclusionHom D i) := by
  unfold productInclusionHom
  simpa only [Fintype.card_fin, Nat.cast_one] using
    (lipschitz_realificationMap (hnil := (D i).filtration.lowerCentralSeries_eq_bot)
      (hM := (pi D).filtration.lowerCentralSeries_eq_bot)
      (D i).basis (pi D).basis (liePiSingle i) 1 (fun k j => productInclusion_matrix_height D i j k))

theorem productSpaceEquiv_symm_coordinate_lipschitz (i : ι) (y : ∀ j, (D j).Space) :
    letI := (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
      (fun a => (productSpaceEquiv D).symm (Function.update y i a)) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L i) := ((D i).basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] (∀ j, L j)) := ((pi D).basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
    ((D i).basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
    ((D i).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := (pi D).metricSpace
  let g : ∀ j, (D j).RealGroup := fun j => (y j).out
  let e := realBCHPiEquiv (fun j => (D j).filtration)
  let u : (pi D).RealGroup := e.symm (Function.update g i 1)
  have hbase : (fun j => (QuotientGroup.mk (g j) : (D j).Space)) = y :=
    funext (fun j => Quotient.out_eq (y j))
  have heval (a : (D i).RealGroup) :
      (productSpaceEquiv D).symm (Function.update y i (QuotientGroup.mk a)) =
        QuotientGroup.mk (productInclusionHom D i a * u) := by
    rw [← hbase, productSpaceEquiv_symm_update_mk]
    have hup : Function.update g i a = Pi.mulSingle i a * Function.update g i 1 := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same, mul_one]
      · simp only [Function.update_of_ne hji, Pi.mul_apply, Pi.mulSingle_eq_of_ne hji, one_mul]
    rw [hup, map_mul, realBCHPiEquiv_symm_single]
  have hm : LipschitzWith 1 (QuotientGroup.mk : (pi D).RealGroup → (pi D).Space) :=
    quotientMetricSpace_lipschitz_mk ((pi D).basis.baseChange ℝ) (pi D).realLattice
      (pi D).realLattice_closed_discrete.1
  have hf := hm.comp ((isometry_mul_right u).lipschitzWith.comp (productInclusionHom_lipschitz D i))
  have hf' : LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
      (fun a : (D i).RealGroup => (productSpaceEquiv D).symm (Function.update y i (QuotientGroup.mk a))) := by
    simpa only [Function.comp_def, one_mul, heval] using hf
  exact rightCosetMetricSpace_lipschitz_lift (D i).realLattice (D i).realLattice_closed_discrete.1 _ hf'

theorem productSpaceEquiv_symm_lipschitz :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (productMetricBound d) (productSpaceEquiv D).symm := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  exact lipschitzWith_of_coordinatewise _ _ (fun i y => productSpaceEquiv_symm_coordinate_lipschitz D i y)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal BigOperators

theorem productMetricBound_le {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) :
    (productMetricBound d : ℝ) ≤ 2 * p * (p ^ 2 + p + 1) := by
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p ^ 2 :=
    sigma_card_le_budget hp hι (fun i => by simpa only [Fintype.card_fin] using hd i)
  have hC (i : ι) : (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1 : ℝ) ≤
      2 * (p ^ 2 + p + 1) := by
    change ((Fintype.card (Σ j, Fin (d j)) : ℝ) + (d i : ℝ) + 1) * (1 + 1) ≤ _
    nlinarith [hd i]
  unfold productMetricBound
  rw [NNReal.coe_sum]
  calc
    _ ≤ ∑ _ : ι, 2 * (p ^ 2 + p + 1) := Finset.sum_le_sum (fun i _ => hC i)
    _ = (Fintype.card ι : ℝ) * (2 * (p ^ 2 + p + 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ p * (2 * (p ^ 2 + p + 1)) := mul_le_mul_of_nonneg_right hι (by positivity)
    _ = _ := by ring

theorem productMetricBound_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) :
    (productMetricBound d : ℝ) ≤ Real.exp ((p + 4) ^ 4) := by
  have hpoly : 2 * p * (p ^ 2 + p + 1) ≤ (p + 4) ^ 4 := by
    nlinarith [sq_nonneg (p ^ 2), mul_nonneg hp (sq_nonneg p)]
  apply (productMetricBound_le d hp hι hd).trans
  exact hpoly.trans (by linarith [Real.add_one_le_exp ((p + 4) ^ 4)])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι σ : Type*} [Fintype ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {w : σ → ℕ} (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w)
  (N : ℕ) [NeZero N]

variable [DecidableEq ι]

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
