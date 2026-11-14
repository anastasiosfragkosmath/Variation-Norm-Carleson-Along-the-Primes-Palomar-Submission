/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeBoundedVariablePatchExpansion.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import OAI.Combinatorics.Progressions.Lattices.PositivePartitionIntegerExpansion
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

noncomputable def productPartitionWeight (j : ∀ a, κ a) (x : ∀ a, X a) : ℝ :=
  ∏ a, ψ a (j a) (x a)

theorem productPartitionWeight_nonneg (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (j : ∀ a, κ a) (x : ∀ a, X a) : 0 ≤ productPartitionWeight ψ j x :=
  Finset.prod_nonneg (fun a _ => hψ a (j a) (x a))

theorem productPartitionWeight_pos_coordinate (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (j : ∀ a, κ a) (x : ∀ a, X a) (hx : 0 < productPartitionWeight ψ j x) (a : α) :
    0 < ψ a (j a) (x a) := by
  classical
  apply lt_of_le_of_ne (hψ a (j a) (x a))
  intro hz
  have hw : productPartitionWeight ψ j x = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ a) hz.symm
  linarith

variable [DecidableEq α] [∀ a, Fintype (κ a)]

theorem sum_productPartitionWeight (hsum : ∀ a x, ∑ j, ψ a j x = 1) (x : ∀ a, X a) :
    ∑ j, productPartitionWeight ψ j x = 1 := by
  unfold productPartitionWeight
  rw [← Fintype.prod_sum (fun a j => ψ a j (x a))]
  simp only [hsum, Finset.prod_const_one]

variable [∀ a, PseudoMetricSpace (X a)]

omit [DecidableEq α] [∀ a, Fintype (κ a)] in
theorem productPartitionWeight_diameter {rho : ℝ} (hrho : 0 ≤ rho)
    (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (hdiam : ∀ a j x y, 0 < ψ a j x → 0 < ψ a j y → dist x y ≤ rho)
    (j : ∀ a, κ a) (x y : ∀ a, X a)
    (hx : 0 < productPartitionWeight ψ j x) (hy : 0 < productPartitionWeight ψ j y) :
    dist x y ≤ rho := by
  apply (dist_pi_le_iff hrho).mpr
  intro a
  exact hdiam a (j a) (x a) (y a)
    (productPartitionWeight_pos_coordinate ψ hψ j x hx a)
    (productPartitionWeight_pos_coordinate ψ hψ j y hy a)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_native_product_partition_approximation (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p rho : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      letI := (pi D).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (v : (pi D).Space → ℂ) (ell : ℝ≥0), LipschitzWith ell v → (∀ x, ‖v x‖ ≤ 2) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖v x - ∑ j, (∏ i, (ψ i (j i) (productProjection D i x) : ℂ)) * c j‖ ≤
                  (ell : ℝ) * (productMetricBound d : ℝ) * rho := by
  obtain ⟨C, hC, hpart⟩ := exists_native_factor_partitions s a
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ _ _ _ _ d D p rho hp hα hD hrho hscale
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, hdiam⟩ :=
    hpart D hp hα hD hrho hscale
  refine ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, ?_⟩
  intro v ell hv hbound
  let F := v ∘ (productSpaceEquiv D).symm
  have hF : LipschitzWith (ell * productMetricBound d) F :=
    hv.comp (productSpaceEquiv_symm_lipschitz D)
  obtain ⟨c, hc, herr⟩ := exists_bounded_complex_partition_approximation
    (productPartitionWeight ψ) (productPartitionWeight_nonneg ψ (fun i j x => (hunit i j x).1))
    (sum_productPartitionWeight ψ hsum)
    (productPartitionWeight_diameter ψ hrho.le (fun i j x => (hunit i j x).1) hdiam)
    F 2 (fun x => hbound _) hF
  refine ⟨c, hc, fun x => ?_⟩
  have h := herr (productSpaceEquiv D x)
  simp only [F, Function.comp_apply, Equiv.symm_apply_apply, productPartitionWeight,
    productSpaceEquiv_apply, NNReal.coe_mul] at h
  push_cast at h
  exact h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_controlled_native_product_approximation (s a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p epsilon : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      letI := (pi D).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (v : (pi D).Space → ℂ) (ell : ℝ≥0),
              (ell : ℝ) ≤ Real.exp ((p + 2) ^ b) → LipschitzWith ell v → (∀ x, ‖v x‖ ≤ 2) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖v x - ∑ j, (∏ i, (ψ i (j i) (productProjection D i x) : ℂ)) * c j‖ ≤ epsilon := by
  obtain ⟨c, _, hpart⟩ := exists_native_product_partition_approximation s 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 2) ^ a + (X + 2) ^ b + (X + 4) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ _ _ _ _ d D p epsilon hp hα hD hepsilon hscale
  let q := p + (p + 2) ^ a + (p + 2) ^ b + (p + 4) ^ 4
  have hpq : p ≤ q := by
    dsimp [q]
    linarith [pow_nonneg (by linarith : 0 ≤ p + 2) a,
      pow_nonneg (by linarith : 0 ≤ p + 2) b, sq_nonneg ((p + 4) ^ 2)]
  have hq : 0 ≤ q := hp.trans hpq
  let A := (p + 2) ^ b + (p + 4) ^ 4
  let rho := epsilon / Real.exp A
  have hrho : 0 < rho := div_pos hepsilon (Real.exp_pos _)
  have hrhoscale : 1 / rho ≤ Real.exp ((q + 2) ^ 1) := by
    calc
      1 / rho = Real.exp A * (1 / epsilon) := by dsimp [rho]; field_simp
      _ ≤ Real.exp A * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
      _ = Real.exp (A + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [A, q]; simp only [pow_one]; linarith)
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happ⟩ :=
    hpart D hq (hα.trans hpq) (fun i => (hD i).mono (D i) hpq) hrho hrhoscale
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hexp := Real.exp_le_exp.mpr hcost
  refine ⟨n, hn, fun i => (hnb i).trans hexp, hcount.trans hexp,
    K, fun i => (hKb i).trans hexp, ψ, hunit, hsum, hLip, ?_⟩
  intro v ell hell hv hb
  obtain ⟨coeff, hcoeff, herr⟩ := happ v ell hv hb
  refine ⟨coeff, hcoeff, fun x => (herr x).trans ?_⟩
  calc
    (ell : ℝ) * (productMetricBound d : ℝ) * rho ≤
        Real.exp ((p + 2) ^ b) * Real.exp ((p + 4) ^ 4) * rho :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hell (productMetricBound_le_exp d hp hα (fun i => (hD i).1))
          (productMetricBound d).coe_nonneg (Real.exp_nonneg _)) hrho.le
    _ = epsilon := by rw [← Real.exp_add]; dsimp [rho, A]; field_simp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI
