/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Nilpotent/LocalNiltestFixedNativePartners.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.SampledNativeModel
@[expose] public section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def withOrbit (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) : D.Niltest v where
  orbit := g
  observable := T.observable
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le := T.norm_le
  lipschitz := T.lipschitz

theorem withOrbit_complexity (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) (p : ℝ) :
    (T.withOrbit g).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem withOrbit_eval (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) (x : τ → ℤ) :
    (T.withOrbit g).eval x = T.observable
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval v x g)) := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L X Y Ω T : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L 0 d} {w : Y → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

variable {L Y Ω T X K : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : Y → ℕ}

end Erdos3

end

end OAI
