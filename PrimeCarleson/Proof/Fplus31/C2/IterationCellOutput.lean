module

public import PrimeCarleson.Proof.Fplus31.C2.IterationTranslate
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIGlue
public import PrimeCarleson.Proof.Fplus31.C2.TypeIGlue

/-!
# The iteration, the sub-step for every window centre

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
extrapolated symbol factorization is a statement about the symbol of the niltest, which
`Niltest.translate` preserves; so the sub-steps `exists_substep` (type I) and
`exists_substep_typeII` apply to the shifted `LengStart` of every window centre `z`. The conclusions
are packaged as `CellOutput` (`IterationFlag.lean`) for the function `x ↦ T.eval (x + z)`:

* `cellOutput_of_extrapolated`: type I, with `K = W + [gr, gr]`; the flag `η [K, K] = 0` is
  `gradedFrequency_lie_eq_zero` applied to the weight-one parts;
* `cellOutput_of_extrapolatedII`: type II, with the flag clauses of the common kernel.

Both give the budget `(p + C)^C` and need the scale `A ≥ e^{(p + C)^C}`.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration

/-- The type I sub-step for the niltest itself (no shift). -/
theorem cellOutput_of_extrapolated_aux (s : ℕ) (hs : s ≤ 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (S : LengStart (s + 1) Q f p) {A : ℝ}, 1 ≤ p → Real.exp ((p + C) ^ C) ≤ A →
      ExtrapolatedSymbolFactorization S.D.filtration S.D.basis S.omega S.hF S.η A
        (S.T.symbol S.D.basis S.omega S.hF) p →
      CellOutput s (fun x => S.T.eval (fun _ => x)) (CommKilled S.η) A ((p + C) ^ C) := by
  obtain ⟨C, hC, h⟩ := exists_substep s hs
  refine ⟨C, hC, fun {Q f p} S {A} hp hA hX => ?_⟩
  obtain ⟨W, K, hWg, hη, hK, hstay, hdrop, -⟩ := h S hp hA hX
  have hB := step2Graded_associatedGraded S.D.filtration S.D.basis S.omega S.hF
    (by have := S.D; omega : s + 1 ≤ 2)
  have hproj : ∀ x ∈ K, basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis
      S.omega S.hF) S.omega 1 x ∈ K := by
    intro x hx
    have hx' : x ∈ W.toSubmodule ⊔ commutatorSubmodule S.D.filtration.AssociatedGraded := by
      rw [← hK]
      exact hx
    obtain ⟨w, hw, c, hcm, rfl⟩ := Submodule.mem_sup.mp hx'
    have h1 : basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega S.hF)
        S.omega 1 (w + c) = basisGradeProjection (S.D.filtration.associatedGradedBasis
        S.D.basis S.omega S.hF) S.omega 1 w := by
      rw [LinearMap.map_add, gradeProjection_one_of_mem_commutator hB hcm, add_zero]
    rw [h1]
    have h2 : basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega S.hF)
        S.omega 1 w ∈ W.toSubmodule ⊔ commutatorSubmodule S.D.filtration.AssociatedGraded :=
      Submodule.mem_sup_left (hWg 1 w hw)
    rw [← hK] at h2
    exact h2
  have hc : ∀ x ∈ K, ∀ y ∈ K,
      S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η ⁅x, y⁆ = 0 := by
    intro x hx y hy
    rw [lie_eq_lie_gradeProjection_one hB x y]
    exact gradedFrequency_lie_eq_zero S.D.filtration S.D.basis S.omega S.hF (by omega)
      (by omega) S.η hWg hη hK (hproj x hx) (hproj y hy)
      (gradeProjection_idem _ _ 1 x) (gradeProjection_idem _ _ 1 y)
  have hd : (∀ z ∈ commutatorSubmodule S.D.filtration.AssociatedGraded,
        S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η z = 0) →
      ∀ x ∈ K, basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega
        S.hF) S.omega (s + 1) x = x →
        S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η x = 0 := fun hflag =>
    gradedFrequency_kills_top_of_flag S.D.filtration S.D.basis S.omega S.hF (by omega)
      (by omega) S.η hWg hη hK (fun x y _ _ => hflag _ (lie_mem_commutator x y))
  exact cellOutput_of_kernel hs S K hc hd hstay hdrop

/-- The type II sub-step for the niltest itself (no shift). -/
theorem cellOutput_of_extrapolatedII_aux (s : ℕ) (hs : s ≤ 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (S : LengStart (s + 1) Q f p) {A : ℝ}, 1 ≤ p → Real.exp ((p + C) ^ C) ≤ A →
      ExtrapolatedSymbolFactorizationII S.D.filtration S.D.basis S.omega S.hF S.η A
        (S.T.symbol S.D.basis S.omega S.hF) p →
      CellOutput s (fun x => S.T.eval (fun _ => x)) (CommKilled S.η) A ((p + C) ^ C) := by
  obtain ⟨C, hC, h⟩ := exists_substep_typeII s hs
  refine ⟨C, hC, fun {Q f p} S {A} hp hA hX => ?_⟩
  obtain ⟨K, -, -, hc, hd, hstay, hdrop, -⟩ := h S hp hA hX
  exact cellOutput_of_kernel hs S K hc hd hstay hdrop

/-- **The type I sub-step for every window centre.** -/
theorem cellOutput_of_extrapolated (s : ℕ) (hs : s ≤ 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (S : LengStart (s + 1) Q f p) {A : ℝ}, 1 ≤ p → Real.exp ((p + C) ^ C) ≤ A →
      ExtrapolatedSymbolFactorization S.D.filtration S.D.basis S.omega S.hF S.η A
        (S.T.symbol S.D.basis S.omega S.hF) p →
      ∀ z : ℤ, CellOutput s (fun x => S.T.eval (fun _ => x + z)) (CommKilled S.η) A
        ((p + C) ^ C) := by
  obtain ⟨C, hC, h⟩ := cellOutput_of_extrapolated_aux s hs
  refine ⟨C, hC, fun {Q f p} S {A} hp hA hX z => ?_⟩
  have hX' : ExtrapolatedSymbolFactorization (S.shift z).D.filtration (S.shift z).D.basis
      (S.shift z).omega (S.shift z).hF (S.shift z).η A
      ((S.shift z).T.symbol (S.shift z).D.basis (S.shift z).omega (S.shift z).hF) p := by
    change ExtrapolatedSymbolFactorization S.D.filtration S.D.basis S.omega S.hF S.η A
      ((S.shift z).T.symbol S.D.basis S.omega S.hF) p
    rw [LengStart.symbol_shift]
    exact hX
  have key := h (S.shift z) hp hA hX'
  have e1 : (fun x : ℤ => (S.shift z).T.eval (fun _ => x)) =
      fun x => S.T.eval (fun _ => x + z) := funext (S.eval_shift z)
  rw [e1] at key
  exact key

/-- **The type II sub-step for every window centre.** -/
theorem cellOutput_of_extrapolatedII (s : ℕ) (hs : s ≤ 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (S : LengStart (s + 1) Q f p) {A : ℝ}, 1 ≤ p → Real.exp ((p + C) ^ C) ≤ A →
      ExtrapolatedSymbolFactorizationII S.D.filtration S.D.basis S.omega S.hF S.η A
        (S.T.symbol S.D.basis S.omega S.hF) p →
      ∀ z : ℤ, CellOutput s (fun x => S.T.eval (fun _ => x + z)) (CommKilled S.η) A
        ((p + C) ^ C) := by
  obtain ⟨C, hC, h⟩ := cellOutput_of_extrapolatedII_aux s hs
  refine ⟨C, hC, fun {Q f p} S {A} hp hA hX z => ?_⟩
  have hX' : ExtrapolatedSymbolFactorizationII (S.shift z).D.filtration (S.shift z).D.basis
      (S.shift z).omega (S.shift z).hF (S.shift z).η A
      ((S.shift z).T.symbol (S.shift z).D.basis (S.shift z).omega (S.shift z).hF) p := by
    change ExtrapolatedSymbolFactorizationII S.D.filtration S.D.basis S.omega S.hF S.η A
      ((S.shift z).T.symbol S.D.basis S.omega S.hF) p
    rw [LengStart.symbol_shift]
    exact hX
  have key := h (S.shift z) hp hA hX'
  have e1 : (fun x : ℤ => (S.shift z).T.eval (fun _ => x)) =
      fun x => S.T.eval (fun _ => x + z) := funext (S.eval_shift z)
  rw [e1] at key
  exact key

end PrimeCarleson.Proof.Fplus31
