/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/LocalMarkedLatticeCorrection.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Fourier.CommonMarkedFrequencyModel
public import OAI.Combinatorics.Progressions.Lattices.MarkedDirectionLatticeScale
public import OAI.Combinatorics.Progressions.Estimates.MarkedUnitOrbit
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem scaledLocalAffineCorrectingElement_mem_realLattice
    {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ) (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) {d : ℕ}
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (hm : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice) (h : ZMod N) :
    D.scaledLocalAffineCorrectingElement t u c h₀ m h ∈ E.realLattice := by
  exact markedDirection_mem_realLattice_of_smul D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t E (m : ℚ)
    (fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))
    (hm (fun i => -affineCyclicTorusCarry u c h₀ h i))

end Erdos3.NativeRankRelation.CommonData

end

end OAI
