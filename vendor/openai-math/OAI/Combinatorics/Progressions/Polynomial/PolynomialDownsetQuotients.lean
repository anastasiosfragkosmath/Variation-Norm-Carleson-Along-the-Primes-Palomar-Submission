/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialDownsetQuotients.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Lie.Prod
public import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
@[expose] public section

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (P : LieSubalgebra ℚ (VectorPolynomial σ ℚ L))

noncomputable def restrictedOutsideDownsetIdeal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) : LieIdeal ℚ P :=
  LieIdeal.comap P.incl (outsideDownsetIdeal J hJ)

@[simp] theorem mem_restrictedOutsideDownsetIdeal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (p : P) :
    p ∈ restrictedOutsideDownsetIdeal P J hJ ↔ ∀ a ∈ J, coefficients p.val a = 0 :=
  mem_outsideDownsetIdeal J hJ p.val

end Erdos3.VectorPolynomial

end

end OAI
