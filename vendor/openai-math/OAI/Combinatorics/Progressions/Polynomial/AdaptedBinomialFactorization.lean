/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/AdaptedBinomialFactorization.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Binomial
public import OAI.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
public import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {σ R : Type*} [CommRing R]

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*}

end Erdos3

end

section

namespace Erdos3

open Polynomial

end Erdos3

end

section

namespace Erdos3

open scoped Pointwise

variable {σ : Type*}

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial Module
open scoped Manifold ContDiff TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitRealEval (w : σ → ℕ) (x : σ → ℝ) :
    F.PolynomialOrbit w →* F.Group :=
  (NilpotentLieBCHGroup.map (eval₂Lie (R := ℚ) (L := L) x)).comp
    (F.polynomialSubgroup w).subtype

@[simp] theorem polynomialOrbitRealEval_coord (w : σ → ℕ)
    (p : F.PolynomialOrbit w) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval w x p).coord = eval₂ x p.log := rfl

theorem polynomialOrbitRealEval_integer (w : σ → ℕ) (p : F.PolynomialOrbit w)
    (x : σ → ℤ) :
    F.polynomialOrbitRealEval w (fun i => (x i : ℝ)) p = F.polynomialOrbitEval w x p := by
  apply NilpotentLieBCHGroup.ext
  simpa only [polynomialOrbitRealEval_coord, polynomialOrbitEval_coord,
    map_intCast] using
    eval₂_algebraMap (S := ℝ) (fun i => (x i : ℚ)) p.log

section Smooth

variable [Fintype ι] [Fintype σ] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

end Smooth
end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

namespace AdaptedMonomial

variable {F} {w : σ → ℕ}

end AdaptedMonomial

noncomputable def adaptedBCHToOrbit (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* F.PolynomialOrbit w :=
  (NilpotentLieBCHGroup.map (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := VectorPolynomial.lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot)
    (F.adaptedLieSubalgebra w).incl).codRestrict _ (fun g => g.coord.property)

namespace AdaptedMonomial

variable {F} {w : σ → ℕ}

end AdaptedMonomial

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

end Real

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F G : NilpotentLieFiltration L s) (hGF : G = F) (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

namespace AdaptedBinomial

variable {F} {w : σ → ℕ}

end AdaptedBinomial
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

end Real
end Erdos3.NilpotentLieFiltration

end

end OAI
