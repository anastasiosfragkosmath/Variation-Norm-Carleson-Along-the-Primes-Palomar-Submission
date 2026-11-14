/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/LieCoordinateScalarExtension.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.BCHDenominatorBudget
@[expose] public section

namespace OAI

section

namespace Erdos3

open MvPolynomial Module

variable {ι X R L : Type*} [Fintype ι] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

theorem lie_coordinate_formula_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ ij : ι × ι, algebraMap ℚ R (c ij.1 ij.2 k) * e.repr a ij.1 * e.repr b ij.2 := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coordinateRightBracket_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (x : X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (coordinateRightBracket c x p k) = e.repr ⁅a, f x⁆ k := by
  simp only [coordinateRightBracket, map_sum, map_mul, aeval_C, aeval_X, hp]
  exact (lie_coordinate_formula_over e c hc a (f x) k).symm

variable [LieAlgebra ℚ L]

theorem coordinateBracketList_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (xs : List X) (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateBracketList c xs p k) = e.repr (rightBracketList f xs a) k := by
  induction xs generalizing p a with
  | nil => exact hp k
  | cons x xs ih =>
    exact ih (coordinateRightBracket c x p) ⁅a, f x⁆
      (coordinateRightBracket_eval_over e c hc f p a hp x)

theorem dynkinCoordinatePolynomial_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (w : FreeSemigroup X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (dynkinCoordinatePolynomial c w k) =
      e.repr (dynkinWord f w) k := by
  apply coordinateBracketList_eval_over e c hc
  intro i
  simp only [aeval_X]

variable [IsScalarTower ℚ R L]

theorem bchCoordinatePolynomial_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (s : ℕ) (a b : L) (k : ι) :
    aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2)
      (bchCoordinatePolynomial c s k) = e.repr (lieBCH s a b) k := by
  change _ = e.coord k (lieBCH s a b)
  rw [lieBCH_bracket_formula]
  simp only [bchCoordinatePolynomial, map_sum, map_mul, aeval_C,
    dynkinCoordinatePolynomial_eval_over e c hc,
    LinearMap.map_smul_of_tower, Algebra.smul_def, Basis.coord_apply]

end Erdos3

end

end OAI
