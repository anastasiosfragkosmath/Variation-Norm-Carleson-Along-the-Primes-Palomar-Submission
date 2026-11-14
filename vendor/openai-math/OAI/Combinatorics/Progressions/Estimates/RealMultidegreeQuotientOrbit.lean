/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/RealMultidegreeQuotientOrbit.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree
public import OAI.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
@[expose] public section

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (I : LieIdeal ℚ L)

theorem realQuotientMultidegree_mem_layer (a : σ → ℕ) {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realification.layer a) :
    realificationLieHom (lieQuotientMap I) x ∈ (F.quotientMultidegree I).realification.layer a := by
  change realificationLieHom (lieQuotientMap I) x ∈
    ((F.layer a).map (lieQuotientMap I).toLinearMap).baseChange ℝ
  rw [realification_map]
  exact ⟨x, hx, rfl⟩

noncomputable def realQuotientMultidegreeMap :
    F.realification.Group →* (F.quotientMultidegree I).realification.Group :=
  realificationMap (hnil := F.ordinary.lowerCentralSeries_eq_bot)
    (hM := (F.quotientMultidegree I).ordinary.lowerCentralSeries_eq_bot) (lieQuotientMap I)

noncomputable def realQuotientMultidegreeOrbit (g : F.realification.PolynomialOrbit) :
    (F.quotientMultidegree I).realification.PolynomialOrbit :=
  (F.quotientMultidegree I).realification.polynomialOrbitOfLog
    (VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
      (PolynomialOrbit.log F.realification g)) (by
        intro a
        rw [coefficients_map]
        exact F.realQuotientMultidegree_mem_layer I (fun i => a i)
          (PolynomialOrbit.adapted F.realification g a))

theorem realQuotientMultidegreeOrbit_eval (g : F.realification.PolynomialOrbit) (x : σ → ℤ) :
    (F.quotientMultidegree I).realification.polynomialOrbitEval x (F.realQuotientMultidegreeOrbit I g) =
      F.realQuotientMultidegreeMap I (F.realification.polynomialOrbitEval x g) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ))
    (VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
      (PolynomialOrbit.log F.realification g)) = _
  rw [eval_map]
  rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
