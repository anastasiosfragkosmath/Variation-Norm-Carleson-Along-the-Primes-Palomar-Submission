/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Geometry/SquarefreeSupportPermutation.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.SquarefreePolynomialPermutation
@[expose] public section

namespace OAI

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def squarefreeSupportModule (P : SquarefreeIndex ι → Prop) :
    Submodule ℚ (SquarefreePolynomial ι L) where
  carrier := {x | ∀ a, ¬P a → squarefreePolynomialEquiv x a = 0}
  zero_mem' := by
    intro a _
    exact congrFun (map_zero squarefreePolynomialEquiv) a
  add_mem' := by
    intro x y hx hy a ha
    rw [map_add, Pi.add_apply, hx a ha, hy a ha, add_zero]
  smul_mem' := by
    intro r x hx a ha
    rw [map_smul, Pi.smul_apply, hx a ha, smul_zero]

theorem squarefreeMonomial_mem_support {P : SquarefreeIndex ι → Prop}
    (a : SquarefreeIndex ι) (ha : P a) (v : L) :
    squarefreeMonomial a v ∈ squarefreeSupportModule P := by
  intro b hb
  exact squarefreePolynomialEquiv_monomial_ne a b
    (fun he => hb (he ▸ ha)) v

end Erdos3

end

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

end Erdos3

end

end OAI
