/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/LatticeSheetHaar.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.OrthogonalBlockGram
public import OAI.Combinatorics.Progressions.Estimates.GramCovolume
public import OAI.Combinatorics.Progressions.Linear.BasisImageSection
public import OAI.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
public import OAI.Combinatorics.Progressions.Linear.SplitSurjectionBasis
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

theorem zspan_covolume_sq_eq_det_gram_fintype
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det := by
  classical
  let e := Fintype.equivFin ι
  let b' := b.reindex e
  have hspan : Submodule.span ℤ (Set.range b') = Submodule.span ℤ (Set.range b) := by
    congr 1
    simp [b', Basis.coe_reindex]
  have hgram : Matrix.gram ℝ b' = (Matrix.gram ℝ b).submatrix e.symm e.symm := by
    ext i j
    simp [b', Matrix.gram_apply]
  have h := zspan_covolume_sq_eq_det_gram b'
  rw [hspan, hgram, Matrix.det_submatrix_equiv_self] at h
  exact h

theorem lattice_covolume_sq_eq_gram
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
    ZLattice.covolume Λ ^ 2 = (Matrix.gram ℝ (b.ofZLatticeBasis ℝ Λ)).det := by
  have h := zspan_covolume_sq_eq_det_gram_fintype (b.ofZLatticeBasis ℝ Λ)
  simpa only [b.ofZLatticeBasis_span ℝ] using h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

end OAI
