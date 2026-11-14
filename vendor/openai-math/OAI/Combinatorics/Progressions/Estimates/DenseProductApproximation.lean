/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/DenseProductApproximation.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.AffinePhaseBias
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_dependent_fin_cons {n : ℕ} {X : Fin (n+1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (∀ i, X i) → M) :
    (𝔼 x, F x) = 𝔼 a : X 0, 𝔼 y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    (𝔼 x, F x) = 𝔼 p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := by
      simpa using (Finset.expect_product' (Finset.univ : Finset (X 0))
        (Finset.univ : Finset (∀ i : Fin n, X i.succ)) (fun a y => F (Fin.cons a y)))

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI
