/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/NumberTheory/SiegelZeros/LocalAlgebra/LocalLength.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Length
@[expose] public section

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem quotient_length_antitone {P Q : Submodule R M} (hPQ : P ≤ Q) :
    Module.length R (M ⧸ Q) ≤ Module.length R (M ⧸ P) :=
  Module.length_le_of_surjective (Submodule.factor hPQ)
    (Submodule.factor_surjective hPQ)

theorem ideal_quotient_length_le {a J : Ideal R} (haJ : a ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ a) :=
  quotient_length_antitone haJ

theorem ideal_quotient_length_le_of_bound {a J : Ideal R} (haJ : a ≤ J)
    {B : ℕ∞} (hbound : Module.length R (R ⧸ a) ≤ B) :
    Module.length R (R ⧸ J) ≤ B :=
  (ideal_quotient_length_le haJ).trans hbound

theorem ideal_quotient_finite_length {a J : Ideal R} (haJ : a ≤ J)
    (ha : IsFiniteLength R (R ⧸ a)) : IsFiniteLength R (R ⧸ J) :=
  ha.of_surjective (Submodule.factor_surjective haJ)

theorem ideal_quotient_length_le_of_degree_bound {a J : Ideal R} (haJ : a ≤ J)
    {degree B : ℕ∞} (hdegree : 1 ≤ degree)
    (hbound : Module.length R (R ⧸ a) * degree ≤ B) :
    Module.length R (R ⧸ J) ≤ B := by
  apply ideal_quotient_length_le_of_bound haJ
  exact (le_mul_of_one_le_right' hdegree).trans hbound

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
