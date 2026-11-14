/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FormalLinearLiftReabsorption.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.ExtractedInitialState
public import OAI.Combinatorics.Progressions.Linear.FormalKernelAbsorption
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ κ ι K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L]

theorem basisPolynomialLift_bound_of_coordinate_bound (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M A τ : ℝ) (hM : 0 ≤ M)
    (hS : ∀ k, CoefficientBound e T M (S k)) (x : K)
    (hx : ‖b.equivFun x‖ ≤ A / τ) :
    CoefficientBound e T ((Fintype.card κ : ℝ) * M * A / τ)
      (basisPolynomialLift b S x) := by
  apply (basisPolynomialLift_coefficientBound b S e T M hS x).mono e T hT
  calc
    (Fintype.card κ : ℝ) * M * ‖b.equivFun x‖ ≤
        (Fintype.card κ : ℝ) * M * (A / τ) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg (Nat.cast_nonneg _) hM)
    _ = _ := by ring

theorem basisPolynomialLift_reabsorption_bound (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M N A τ : ℝ) (hM : 0 ≤ M)
    (hS : ∀ k, CoefficientBound e T M (S k))
    (small : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : CoefficientBound e T (N / τ) small)
    (x : K) (hx : ‖b.equivFun x‖ ≤ A / τ) :
    CoefficientBound e T ((N + (Fintype.card κ : ℝ) * M * A) / τ)
      (small + basisPolynomialLift b S x) := by
  have h := basisPolynomialLift_bound_of_coordinate_bound b S e T hT M A τ hM hS x hx
  have hsum := hsmall.sub e T (h.neg e T)
  rw [sub_neg_eq_add] at hsum
  convert hsum using 1
  ring

theorem basisPolynomialLift_reabsorption_grid (b : Basis κ ℝ K)
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (l m n : ℕ) (hR : ∀ k, CoefficientGrid e m (R k))
    (rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : CoefficientGrid e n rational)
    (x : K) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    CoefficientGrid e (n * (m * l)) (rational + basisPolynomialLift b R x) := by
  have h := basisPolynomialLift_coefficientGrid b R e l m hR x hx
  intro α
  have hsum := realDenominatorGrid_sub_product n (m * l)
    (fun i => e.repr (coefficients rational α) i)
    (-(fun i => e.repr (coefficients (basisPolynomialLift b R x) α) i))
    (hrational α) (realDenominatorGrid_neg (m * l) (h α))
  simp only [sub_neg_eq_add] at hsum
  simp only [map_add, Finsupp.add_apply]
  exact hsum

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ κ ι K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥}

end NilpotentLieBCHGroup

end Erdos3

end

end OAI
