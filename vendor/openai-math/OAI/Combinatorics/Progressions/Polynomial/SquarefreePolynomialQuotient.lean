/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/SquarefreePolynomialQuotient.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.LinearAlgebra.Isomorphisms
public import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
@[expose] public section

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

abbrev SquarefreePolynomial (ι L : Type*) [LieRing L] [LieAlgebra ℚ L] :=
  VectorPolynomial ι ℚ L ⧸ (squarefreePolynomialIdeal (ι := ι) (L := L))

noncomputable def squarefreeMk : VectorPolynomial ι ℚ L →ₗ⁅ℚ⁆ SquarefreePolynomial ι L :=
  lieQuotientMap squarefreePolynomialIdeal

theorem squarefreeMk_monomial_zero (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) (v : L) :
    squarefreeMk (monomial a v) = (0 : SquarefreePolynomial ι L) :=
  (lieQuotientMap_eq_zero _ _).mpr (monomial_mem_squarefreeKernel a ha v)

noncomputable def squarefreeMonomial (a : SquarefreeIndex ι) : L →ₗ[ℚ] SquarefreePolynomial ι L where
  toFun v := squarefreeMk (monomial a.val v)
  map_add' v w := by simp only [monomial, TensorProduct.tmul_add, map_add]
  map_smul' r v := by simp only [monomial, TensorProduct.tmul_smul, map_smul, RingHom.id_apply]

theorem squarefreeMonomial_apply (a : SquarefreeIndex ι) (v : L) :
    squarefreeMonomial a v = squarefreeMk (monomial a.val v) := rfl

noncomputable def squarefreePolynomialEquiv [Fintype ι] :
    SquarefreePolynomial ι L ≃ₗ[ℚ] (SquarefreeIndex ι → L) :=
  LinearMap.quotKerEquivOfSurjective (squarefreeCoefficients (ι := ι) (L := L))
    (squarefreeCoefficients_surjective (ι := ι) (L := L))

@[simp] theorem squarefreePolynomialEquiv_mk [Fintype ι] (p : VectorPolynomial ι ℚ L) :
    squarefreePolynomialEquiv (squarefreeMk p) = squarefreeCoefficients p := rfl

theorem squarefreePolynomialEquiv_monomial_self [Fintype ι] (a : SquarefreeIndex ι) (v : L) :
    squarefreePolynomialEquiv (squarefreeMonomial a v) a = v :=
  squarefreeCoefficients_monomial_self a v

theorem squarefreePolynomialEquiv_monomial_ne [Fintype ι]
    (a b : SquarefreeIndex ι) (hab : a ≠ b) (v : L) :
    squarefreePolynomialEquiv (squarefreeMonomial a v) b = 0 :=
  squarefreeCoefficients_monomial_ne a b hab v

theorem sum_squarefreeMonomial [Fintype ι] (x : SquarefreePolynomial ι L) :
    (∑ a : SquarefreeIndex ι, squarefreeMonomial a (squarefreePolynomialEquiv x a)) = x := by
  classical
  apply squarefreePolynomialEquiv.injective
  ext b
  simp only [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single b]
  · exact squarefreePolynomialEquiv_monomial_self b _
  · intro a _ h
    exact squarefreePolynomialEquiv_monomial_ne a b h _
  · simp

end Erdos3

end

end OAI
