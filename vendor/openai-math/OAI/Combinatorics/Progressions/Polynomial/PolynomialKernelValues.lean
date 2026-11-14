/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialKernelValues.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import OAI.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
public import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
public import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceHom
public import OAI.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice
public import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse
public import OAI.Combinatorics.Progressions.Polynomial.PolynomialTermCount
public import OAI.Combinatorics.Progressions.Linear.RationalMatrixSeparation
@[expose] public section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

noncomputable def eval₂ (x : σ → S) : VectorPolynomial σ R V →ₗ[R] V :=
  TensorProduct.lift ((Algebra.lsmul R R V).toLinearMap.comp (MvPolynomial.aeval x).toLinearMap)

@[simp] theorem eval₂_tmul (x : σ → S) (p : MvPolynomial σ R) (v : V) :
    eval₂ x (p ⊗ₜ[R] v) = MvPolynomial.aeval x p • v := rfl

@[simp] theorem eval₂_monomial (x : σ → S) (α : σ →₀ ℕ) (v : V) :
    eval₂ x (monomial (R := R) α v) = (α.prod fun i n => x i ^ n) • v := by
  simp [monomial, MvPolynomial.aeval_monomial]

theorem eval₂_algebraMap (x : σ → R) (p : VectorPolynomial σ R V) :
    eval₂ (fun i => algebraMap R S (x i)) p = eval x p := by
  have heval (q : MvPolynomial σ R) :
      MvPolynomial.aeval (fun i => algebraMap R S (x i)) q =
        algebraMap R S (MvPolynomial.aeval x q) := by
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  induction p using TensorProduct.inductionOn with
  | tmul q v => simp only [eval₂_tmul, eval_tmul, heval, IsScalarTower.algebraMap_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem coordinate_eval₂ (f : V →ₗ[S] S) (x : σ → S) (p : VectorPolynomial σ R V) :
    f (eval₂ x p) = MvPolynomial.eval x (coordinate f.toAddMonoidHom p) := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, coordinate_sum, coordinate_monomial,
    eval₂_monomial, MvPolynomial.eval_monomial, map_smul, smul_eq_mul, mul_comm]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

variable {X D E : Type*}

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {σ R V : Type*} [Fintype σ]
  [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def linearPolynomial : (σ → V) →ₗ[R] VectorPolynomial σ R V where
  toFun a := ∑ i, monomial (Finsupp.single i 1) (a i)
  map_add' a b := by
    simp only [Pi.add_apply, monomial, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, monomial, TensorProduct.tmul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem linearPolynomial_apply (a : σ → V) :
    linearPolynomial (R := R) a = ∑ i, monomial (Finsupp.single i 1) (a i) := rfl

theorem coefficients_linearPolynomial_single (a : σ → V) (i : σ) :
    coefficients (linearPolynomial (R := R) a) (Finsupp.single i 1) = a i := by
  rw [linearPolynomial_apply, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · rw [coefficients_monomial, Finsupp.single_eq_same]
  · intro j _ hji
    rw [coefficients_monomial, Finsupp.single_eq_of_ne]
    exact fun h => hji ((Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)) h.symm)
  · simp

theorem coefficients_linearPolynomial_of_ne (a : σ → V) (α : σ →₀ ℕ)
    (hα : ∀ i, Finsupp.single i 1 ≠ α) : coefficients (linearPolynomial (R := R) a) α = 0 := by
  rw [linearPolynomial_apply, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [coefficients_monomial, Finsupp.single_eq_of_ne (Ne.symm (hα i))]

@[simp] theorem coefficients_linearPolynomial_zero (a : σ → V) :
    coefficients (linearPolynomial (R := R) a) 0 = 0 := by
  apply coefficients_linearPolynomial_of_ne
  intro i h
  have hi := congrArg (fun α : σ →₀ ℕ => α i) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply, Nat.one_ne_zero] at hi

theorem eval₂_linearPolynomial {S : Type*} [CommRing S] [Algebra R S]
    [Module S V] [IsScalarTower R S V] (a : σ → V) (t : σ → S) :
    eval₂ t (linearPolynomial (R := R) a) = ∑ i, t i • a i := by
  simp [linearPolynomial_apply, eval₂_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R S V : Type*} [Finite σ] [CommRing R] [Field S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Erdos3.VectorPolynomial

end

section

open scoped Matrix

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix
open VectorPolynomial

variable {η κ σ : Type*} [Fintype κ] {ρ : η → Type*}

end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial

open scoped Matrix
open VectorPolynomial

end Erdos3

end

end OAI
