/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/NumberTheory/SiegelZeros/Selection/InvariantBox.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.NumberTheory.SiegelZeros.Differentials.InvariantDerivation
public import OAI.NumberTheory.SiegelZeros.LocalAlgebra.BoxPolynomials
@[expose] public section

namespace OAI

namespace SiegelZeros


namespace W17

variable {K : Type*} [Field K]

theorem invariantDerivation_mem_boxPolynomials (v : Fin 4 → K) {N : ℕ}
    {F : MvPolynomial (Fin 4) K} (hF : F ∈ boxPolynomials K N) :
    WeightedTorusJets.W18.invariantDerivation v F ∈ boxPolynomials K N :=
  WeightedTorusJets.W18.inBox_invariantDerivation v hF

end W17


end SiegelZeros

end OAI
