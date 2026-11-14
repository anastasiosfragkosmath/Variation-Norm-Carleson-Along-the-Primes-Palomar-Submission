/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/MarkedEvaluationJointBounds.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Geometry.MarkedDirectionCoordinates
@[expose] public section

namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)

include hω hH hc in
theorem markedShiftBasis_structure_height (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) :
    let U := max (lieTreeHeight (Fintype.card ι) H s) (s + 1)
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∀ i j k, RationalHeightLE (lieStructureConstants e i j k)
      (rationalLieStructureHeight a (max U (rationalSolveHeight d U))) := by
  classical
  let U := max (lieTreeHeight (Fintype.card ι) H s) (s + 1)
  have hHU : H ≤ U := (lieTreeHeight_ge_input _ _ _).trans (Nat.le_max_left _ _)
  have hU : 1 ≤ U := hH.trans hHU
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  let E := F.associatedDegree.polynomialShiftBasis b ω hF t
  have hCE (i j k) : RationalHeightLE (lieStructureConstants E i j k) U :=
    (F.associatedDegree.polynomialShiftBasis_structure_height b ω hF hω hH hc t i j k).mono
      (max_le hHU (Nat.le_max_right _ _))
  have hmatrix (i j) : RationalHeightLE
      (LinearMap.toMatrix e E (markedShiftSubalgebra F v w marked t).incl.toLinearMap i j) U := by
    rw [LinearMap.toMatrix_apply]
    exact (he j i).mono (Nat.le_max_left _ _)
  obtain ⟨_, _, _, hstructure⟩ := exists_bounded_lie_embedding_retraction e E
    (markedShiftSubalgebra F v w marked t).incl (fun _ _ h => Subtype.ext h) hU hCE hmatrix
  dsimp only
  intro i j k
  simpa only [Fintype.card_fin, ← finrank_eq_card_basis E] using hstructure i j k

end Erdos3

end

section

namespace Erdos3

open Module

def markedQuotientHeight (s n a d m q H : ℕ) : ℕ :=
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  let J := max 1 (max C Q)
  max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
    ((d + 1) * (B * Q) ^ d)

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

def markedEvaluationHeight (s n a d m q H K : ℕ) : ℕ :=
  let T := lieTreeHeight n H s
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let Q := rationalKernelHeight m B
  max (markedQuotientHeight s n a d m q H)
    ((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d)

variable {I ι ν L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hw hv hH hc hgen in
theorem exists_markedShiftQuotient_bounded_evaluation_data (t : ℕ)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
    (hcoef : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t),
        let R := markedEvaluationHeight s (Fintype.card ι) a d m q H K
        (∀ i j k, RationalHeightLE (lieStructureConstants f i j k) R) ∧
        (∀ α : Fin 2 → ℕ,
          ∃ e : Basis (Fin (finrank ℚ (markedShiftQuotientLayer F v w marked t α))) ℚ
              (markedShiftQuotientLayer F v w marked t α),
            ∀ i j, RationalHeightLE (f.repr (e i).val j) R) ∧
        (∀ i j, RationalHeightLE
          (f.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) R) ∧
        (∀ i j, RationalHeightLE (markedQuotientPhase F v w marked t (f j) i) R) ∧
        ∀ i j, RationalHeightLE (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (f j)) i) R := by
  classical
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  let T := lieTreeHeight (Fintype.card ι) H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  obtain ⟨e, he⟩ := exists_markedShift_bounded_basis F b ω hF v w marked hw hv hH hc hgen hω t
  obtain ⟨m, hm, q, hq, f, hf⟩ := exists_markedShiftQuotient_bounded_coordinates
    F b ω hF v w marked hw hv hH hc hgen hω t e he
  let Q := rationalKernelHeight m B
  let V := max 1 (max C Q)
  let A := max T ((Fintype.card ι + 1) * (T * K) ^ Fintype.card ι)
  let G := markedQuotientHeight s (Fintype.card ι) a d m q H
  let R := markedEvaluationHeight s (Fintype.card ι) a d m q H K
  have hGR : G ≤ R := Nat.le_max_left _ _
  have hT : 1 ≤ T := hH.trans (lieTreeHeight_ge_input _ _ _)
  have hsolve := rationalSolveHeight_pos d hT
  have hB : 1 ≤ B := by
    dsimp [B]
    have := Nat.zero_lt_of_lt hT
    exact Nat.succ_le_iff.mpr (by positivity)
  have hQ : 1 ≤ Q := rationalKernelHeight_pos m hB
  have hC : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) C :=
    markedShiftBasis_structure_height F b ω hF hω v w marked hH hc t e he
  have hproj : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q := hf
  have hmatrix (i j) : RationalHeightLE
      (LinearMap.toMatrix e f (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap i j) V := by
    rw [LinearMap.toMatrix_apply]
    exact (hproj i j).mono ((Nat.le_max_right C Q).trans (Nat.le_max_right 1 _))
  obtain ⟨_, _, _, hstructure⟩ := exists_bounded_lie_quotient_section e f
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)) (lieQuotientMap_surjective _)
    (Nat.le_max_left 1 (max C Q))
    (fun i j k => (hC i j k).mono ((Nat.le_max_left C Q).trans (Nat.le_max_right 1 _))) hmatrix
  have hphaseR : (d + 1) * (rationalSolveHeight q Q * T) ^ d ≤ R := by
    apply le_trans _ (Nat.le_max_right G _)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_max_left _ _)) _)
  have hevalR : (d + 1) *
      (rationalSolveHeight q Q * ((Fintype.card ι + 1) * (T * K) ^ Fintype.card ι)) ^ d ≤ R := by
    apply le_trans _ (Nat.le_max_right G _)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_max_right _ _)) _)
  refine ⟨m, hm, q, hq, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j k
    apply RationalHeightLE.mono _ hGR
    change RationalHeightLE _ (max (rationalLieStructureHeight d (max V (rationalSolveHeight q V)))
      ((d + 1) * (B * Q) ^ d))
    apply RationalHeightLE.mono _ (Nat.le_max_left _ _)
    simpa only [Fintype.card_fin] using hstructure i j k
  · intro α
    obtain ⟨e', he'⟩ := exists_markedShiftQuotientLayer_bounded_basis
      F b ω hF v w marked hw hv hH hc hgen hω t e he f hproj α
    refine ⟨e', ?_⟩
    intro i j
    exact (he' i j).mono ((Nat.le_max_right _ _).trans hGR)
  · intro i j
    exact (markedQuotientDirection_coordinate_height F v w marked t b ω hF hω hT
      e he f hproj i j).mono ((Nat.le_max_right _ _).trans hGR)
  · intro i j
    exact (markedQuotientPhase_coordinate_height F v w marked t b ω hF e he f hQ hproj i j).mono hphaseR
  · intro i j
    exact (markedBaseEvaluation_zero_coordinate_height F v w marked t b ω hF e he f hQ hproj
      J hJ c hcoef i j).mono hevalR

end Erdos3

end

end OAI
