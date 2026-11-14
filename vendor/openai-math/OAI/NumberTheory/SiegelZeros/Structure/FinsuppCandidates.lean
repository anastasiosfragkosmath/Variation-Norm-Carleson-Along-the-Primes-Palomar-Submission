/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/NumberTheory/SiegelZeros/Structure/FinsuppCandidates.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ParameterCombinations
@[expose] public section

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

variable {k σ ι : Type*} [CommRing k]

theorem linearCombination_eq_parameterCombination (f : ι → MvPolynomial σ k) (c : ι →₀ k) :
    Finsupp.linearCombination k f c = parameterCombination c.support c f := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, parameterCombination,
    MvPolynomial.C_mul']

theorem linearCombination_totalDegree_le (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    {d : ℕ} (hf : ∀ i, (f i).totalDegree ≤ d) :
    (Finsupp.linearCombination k f c).totalDegree ≤ d := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_totalDegree_le c.support c f (fun i _ => hf i)

theorem linearCombination_mem_ideal (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    (J : Ideal (MvPolynomial σ k)) (hf : ∀ i, f i ∈ J) :
    Finsupp.linearCombination k f c ∈ J := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_mem c.support c f J (fun i _ => hf i)

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
