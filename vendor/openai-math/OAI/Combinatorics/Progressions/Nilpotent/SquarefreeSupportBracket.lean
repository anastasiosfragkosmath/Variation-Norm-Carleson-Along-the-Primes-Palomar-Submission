/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/SquarefreeSupportBracket.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.SquarefreeSupportPermutation
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeSupportModule_lie_mem {P Q R : SquarefreeIndex ι → Prop}
    (h : ∀ a b (hab : Disjoint a.val.support b.val.support),
      P a → Q b → R (a.disjointAdd b hab))
    {x y : SquarefreePolynomial ι L}
    (hx : x ∈ squarefreeSupportModule P) (hy : y ∈ squarefreeSupportModule Q) :
    ⁅x, y⁆ ∈ squarefreeSupportModule R := by
  classical
  rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  by_cases ha : P a
  · by_cases hb : Q b
    · by_cases hab : Disjoint a.val.support b.val.support
      · rw [squarefreeMonomial_lie_disjoint a b hab]
        exact squarefreeMonomial_mem_support _ (h a b hab ha hb) _
      · rw [squarefreeMonomial_lie_overlap a b hab]
        exact (squarefreeSupportModule R).zero_mem
    · rw [hy b hb, map_zero, lie_zero]
      exact (squarefreeSupportModule R).zero_mem
  · rw [hx a ha, map_zero, zero_lie]
    exact (squarefreeSupportModule R).zero_mem

end Erdos3

end

end OAI
