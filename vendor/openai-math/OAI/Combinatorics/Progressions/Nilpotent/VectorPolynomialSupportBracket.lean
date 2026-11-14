/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/VectorPolynomialSupportBracket.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
@[expose] public section

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem coefficientSupport_lie {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {S T U : Set (σ →₀ ℕ)} (hST : ∀ a ∈ S, ∀ b ∈ T, a + b ∈ U)
    {p q : VectorPolynomial σ R L}
    (hp : p ∈ coefficientSupport S) (hq : q ∈ coefficientSupport T) :
    ⁅p, q⁆ ∈ coefficientSupport U := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum]
  apply (coefficientSupport U).sum_mem
  intro a ha
  apply (coefficientSupport U).sum_mem
  intro b hb
  rw [lie_monomial]
  apply monomial_mem_coefficientSupport
  apply hST
  · by_contra h
    exact (Finsupp.mem_support_iff.mp ha) (hp a h)
  · by_contra h
    exact (Finsupp.mem_support_iff.mp hb) (hq b h)

end Erdos3.VectorPolynomial

end

end OAI
