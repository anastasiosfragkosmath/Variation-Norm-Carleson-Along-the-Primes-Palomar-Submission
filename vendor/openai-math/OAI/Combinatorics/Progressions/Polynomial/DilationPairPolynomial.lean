/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/DilationPairPolynomial.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization
@[expose] public section

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def dilationPair (w : σ → ℕ) (q : ℚ) (p : VectorPolynomial σ ℚ L) :
    VectorPolynomial σ ℚ (L × L) := pair (weightedDilation w q p) p

@[simp] theorem coefficients_dilationPair (w : σ → ℕ) (q : ℚ)
    (p : VectorPolynomial σ ℚ L) (a : σ →₀ ℕ) :
    coefficients (dilationPair w q p) a =
      (q ^ Finsupp.weight w a • coefficients p a, coefficients p a) := by
  simp only [dilationPair, coefficients_pair, coefficients_weightedDilation]

theorem eval_dilationPair (w : σ → ℕ) (q : ℚ) (p : VectorPolynomial σ ℚ L) (x : σ → ℚ) :
    eval x (dilationPair w q p) = (eval (fun i => q ^ w i * x i) p, eval x p) := by
  simp only [dilationPair, eval_pair, eval_weightedDilation]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem dilationPair_coefficients (w : σ → ℕ) (q : ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (a : σ →₀ ℕ) :
    coefficients (dilationPair w q p) a ∈ F.dilationPairLayer q (Finsupp.weight w a) := by
  rw [coefficients_dilationPair, F.mem_dilationPairLayer]
  have ha := (F.adapted_iff_coefficients w p).mp hp a
  exact ⟨(F.layer _).smul_mem _ ha, ha, by simp⟩

end NilpotentLieFiltration

end Erdos3

end

end OAI
