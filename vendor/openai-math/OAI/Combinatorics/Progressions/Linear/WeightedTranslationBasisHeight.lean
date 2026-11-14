/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Linear/WeightedTranslationBasisHeight.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.LinearAlgebra.Basis.Prod
public import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
public import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
@[expose] public section

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module

variable {σ : Type*} [Fintype σ]

abbrev WeightedBasisIndex (w : σ → ℕ) (d : ℕ) :=
  σ ⊕ {a : σ →₀ ℕ | Finsupp.weight w a < d}

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) {H : ℕ}

end Erdos3.PolynomialTranslationLie

end

end OAI
