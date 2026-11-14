module

public import PrimeCarleson.Proof.Fplus31.C2.TypeIIClone
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIPair
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIAlg
public import PrimeCarleson.Proof.Fplus31.Extrapolation.MainII

/-!
# The extrapolation step, type II variant, instantiated on the pair model `D × D`

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
abstract type II extrapolation of the abstract extrapolation
(`symbol_dilation_extrapolation_typeII`) is stated for the product `g × g` of the abstract model.
Here it is instantiated on the vendored library's types: the symbol of the product orbit of `D × D`
(`C2/TypeIIPair.lean`) is identified with the pair `(δ_{qℓ} X, δ_{qℓ'} X)` of the abstract model by
the index equivalence `pairEquiv` (`C2/TypeIIAlg.lean`), a `ControlledSymbolFactorization` of the
pair model for the frequency `(η, -η)` becomes a `Datum` (`C2/Symbol.lean`,
`datum_of_controlledSymbolFactorization`), and the common kernel `K⁰` of the conclusion gives an
`ExtrapolatedSymbolFactorizationII` (`C2/TypeIIClone.lean`). The dictionary is generic, so `pi D`
only needs `Step2Graded` for the product basis, which is `step2Graded_associatedGraded` for the
product filtration.

* `symbolGroupEquiv_symm_fst`, `symbolGroupEquiv_symm_snd`, `gradeProjection_top_eq`: generic
  coordinate facts of the dictionary;
* `frLin_equiv`, `frLin_sumElim`, `elim_map_val`: reindexing of the layer functionals;
* `pairEquiv`, `pair_gradedFrequency`: the identification of `gr (D × D)` with the product and
  of the graded frequency `(η, -η)` with `frPair`;
* `single_dil_repr_fst`, `single_dil_repr_snd`, `pair_map_eq_biDil`: the transport of the symbol of
  a pair orbit is `biDil`;
* `symbol_dilation_extrapolation_typeII_clone`: the library-level statement.

-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section Helpers

/-- Reindexing of `frLin`. -/
theorem frLin_equiv {κ ι : Type*} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (μ : κ → ℚ) (μ' : ι → ℚ)
    (h : ∀ k, μ k = μ' (e k)) (z : ι → ℚ) :
    frLin μ (fun k => z (e k)) = frLin μ' z := by
  simp only [frLin_apply, h]
  exact e.sum_comp (fun i => z i * μ' i)

/-- `frLin` of the weights `(μ, -μ)` is `frPair μ`. -/
theorem frLin_sumElim {ι : Type*} [Fintype ι] (μ : ι → ℚ) (z : ι ⊕ ι → ℚ) :
    frLin (Sum.elim μ (fun j => -μ j)) z = frPair μ z := by
  simp [frLin_apply, frPair_apply, Fintype.sum_sum_type, sub_eq_add_neg, Finset.sum_neg_distrib]

/-- `Sum.elim` after `Sum.map Subtype.val Subtype.val`. -/
theorem elim_map_val {α : Type*} {P : α → Prop} (f g : α → ℚ) (u : {x // P x} ⊕ {x // P x}) :
    Sum.elim f g (Sum.map Subtype.val Subtype.val u) =
      Sum.elim (fun x : {x // P x} => f x.1) (fun x : {x // P x} => g x.1) u := by
  rcases u with u | u <;> rfl

end Helpers

section Generic

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

/-- The weight-one coordinates of the abstract element corresponding to a symbol. -/
theorem symbolGroupEquiv_symm_fst (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (Y : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)) (u : Idx1 ω) :
    ((symbolGroupEquiv F b ω hF hs1 hs2).symm Y).fst u =
      ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr Y.coord u.1 := by
  have kE1 : ∀ (Z : SymbolGroup (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω))
      (i : Idx1 ω), ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (symbolGroupEquiv F b ω hF hs1 hs2 Z).coord i.1 = Z.fst i :=
    fun Z i => repr_realElt_fst _ ω Z i
  have := kE1 ((symbolGroupEquiv F b ω hF hs1 hs2).symm Y) u
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

/-- The weight-two coordinates of the abstract element corresponding to a symbol. -/
theorem symbolGroupEquiv_symm_snd (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (Y : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)) (u : Idx2 ω) :
    ((symbolGroupEquiv F b ω hF hs1 hs2).symm Y).snd u =
      ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr Y.coord u.1 := by
  have kE2 : ∀ (Z : SymbolGroup (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω))
      (k : Idx2 ω), ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (symbolGroupEquiv F b ω hF hs1 hs2 Z).coord k.1 = Z.snd k :=
    fun Z k => repr_realElt_snd _ ω Z k
  have := kE2 ((symbolGroupEquiv F b ω hF hs1 hs2).symm Y) u
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end Generic

section Proj

variable {V : Type*} [LieRing V] [LieAlgebra ℚ V] {ι : Type*} [Fintype ι]
  {B : Module.Basis ι ℚ V} {ω : ι → ℕ}

/-- A vector of the top layer (weight `s ∈ {1, 2}`) is fixed by the top projection. -/
theorem gradeProjection_top_eq (hB : Step2Graded B ω) {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (x : V)
    (h2 : s = 2 → (phi hB x).1 = 0) (h1 : s = 1 → (phi hB x).2 = 0) :
    basisGradeProjection B ω s x = x := by
  apply (phi hB).injective
  rcases (by omega : s = 1 ∨ s = 2) with rfl | rfl
  · rw [phi_gradeProjection_one]
    exact Prod.ext rfl (h1 rfl).symm
  · rw [phi_gradeProjection_two]
    exact Prod.ext (h2 rfl).symm rfl

end Proj

section PairB5

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {ω : Fin d → ℕ}
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

/-- **The identification of `gr (D × D)` with the product `(gr D) × (gr D)` of the abstract
model.** -/
def pairEquiv :
    Step2Algebra.IndexEquiv (stepTwoAlgebra (pairAssoc D ω hF) (pairWeight ω))
      (stepTwoAlgebra (singleAssoc D ω hF) ω).prod :=
  ⟨pairIdx ω 1, pairIdx ω 2, fun i j k => pair_c_eq hF i j k⟩

/-- **The graded frequency of the pair model, in the coordinates of the product.** -/
theorem pair_gradedFrequency (hB : Step2Graded (pairAssoc D ω hF) (pairWeight ω))
    (η : L →ₗ[ℚ] ℚ)
    (w : (Idx1 ω ⊕ Idx1 ω → ℚ) × (Idx2 ω ⊕ Idx2 ω → ℚ)) :
    (pairModel D).filtration.gradedFrequency (pairModel D).basis (pairWeight ω) (pairLayers hF)
      (pairFreq η) ((phi hB).symm ((pairEquiv hF).psi.symm w)) =
      frPair (fun i : Idx1 ω => η (D.basis i.1)) w.1 +
        frPair (fun k : Idx2 ω => η (D.basis k.1)) w.2 := by
  rw [gradedFrequency_phi_symm]
  congr 1
  · rw [← frLin_sumElim]
    exact frLin_equiv (pairIdx ω 1) _ _ (fun i => by
      change pairFreq η ((pairModel D).basis i.1) = _
      rw [pairFreq_basis, ← pairIdx_val ω 1 i]
      exact elim_map_val (P := fun j : Fin d => ω j = 1) (fun j => η (D.basis j))
        (fun j => -η (D.basis j)) (pairIdx ω 1 i)) w.1
  · rw [← frLin_sumElim]
    exact frLin_equiv (pairIdx ω 2) _ _ (fun i => by
      change pairFreq η ((pairModel D).basis i.1) = _
      rw [pairFreq_basis, ← pairIdx_val ω 2 i]
      exact elim_map_val (P := fun j : Fin d => ω j = 2) (fun j => η (D.basis j))
        (fun j => -η (D.basis j)) (pairIdx ω 2 i)) w.2


/-- The first-layer coordinates of the dilated symbol: `r` times those of the symbol. -/
theorem single_dil_repr_fst (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (r : ℚ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1)) (j : Idx1 ω) :
    ((singleAssoc D ω hF).baseChange ℝ).repr
      (D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1) r X).coord j.1 =
      (r : ℝ) * ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X).fst j := by
  have h := symbolGroupEquiv_dil D.filtration D.basis ω hF hs1 hs2 r
    ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h]
  refine (repr_realElt_fst (singleAssoc D ω hF) ω (SymbolGroup.dil (r : ℝ)
    ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X)) j).trans ?_
  simp

/-- The second-layer coordinates of the dilated symbol: `r²` times those of the symbol. -/
theorem single_dil_repr_snd (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (r : ℚ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1)) (k : Idx2 ω) :
    ((singleAssoc D ω hF).baseChange ℝ).repr
      (D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1) r X).coord k.1 =
      (r : ℝ) ^ 2 * ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X).snd k := by
  have h := symbolGroupEquiv_dil D.filtration D.basis ω hF hs1 hs2 r
    ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h]
  refine (repr_realElt_snd (singleAssoc D ω hF) ω (SymbolGroup.dil (r : ℝ)
    ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X)) k).trans ?_
  simp

/-- **The abstract pair `(δ_{r₀} X, δ_{r₁} X)` is the transport of the symbol of the pair orbit.**
If the coordinates of `Y` in `gr (D × D)` are those of `δ_{r₀} X` on the first block and
`δ_{r₁} X` on the second, then the transport of `Y` to the product model is `biDil r₀ r₁ X`. -/
theorem pair_map_eq_biDil (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (r₀ r₁ : ℚ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (Y : (pairModel D).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (hY : ∀ k : Fin (Fintype.card (Σ _ : Fin 2, Fin d)),
      ((pairAssoc D ω hF).baseChange ℝ).repr Y.coord k =
        ((singleAssoc D ω hF).baseChange ℝ).repr
          (D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1)
            (if ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).1 = 0 then r₀ else r₁) X).coord
          ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).2) :
    (pairEquiv hF).map ((symbolGroupEquiv (pairModel D).filtration (pairModel D).basis
      (pairWeight ω) (pairLayers hF) hs1 hs2).symm Y) =
      SymbolGroup.biDil (r₀ : ℝ) (r₁ : ℝ)
        ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X) := by
  have hYfst := symbolGroupEquiv_symm_fst (pairModel D).filtration (pairModel D).basis
    (pairWeight ω) (pairLayers hF) hs1 hs2 Y
  have hYsnd := symbolGroupEquiv_symm_snd (pairModel D).filtration (pairModel D).basis
    (pairWeight ω) (pairLayers hF) hs1 hs2 Y
  have h0 : ∀ j : Fin d, (if ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm
      (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨0, j⟩)).1 = 0 then r₀ else r₁) = r₀ := fun j => by
    rw [Equiv.symm_apply_apply]
    exact ite_eq_left rfl
  have h1 : ∀ j : Fin d, (if ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm
      (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨1, j⟩)).1 = 0 then r₀ else r₁) = r₁ := fun j => by
    rw [Equiv.symm_apply_apply]
    exact ite_eq_right (by change ¬ (1 : Fin 2) = 0; decide)
  refine SymbolGroup.ext ?_ ?_
  · funext u
    rcases u with j | j
    · change ((symbolGroupEquiv (pairModel D).filtration (pairModel D).basis (pairWeight ω)
        (pairLayers hF) hs1 hs2).symm Y).fst ((pairIdx ω 1).symm (Sum.inl j)) =
        (r₀ : ℝ) * ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X).fst j
      rw [hYfst]
      have h3 := hY (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨0, j.1⟩)
      rw [h0, Equiv.symm_apply_apply] at h3
      exact h3.trans (single_dil_repr_fst hF hs1 hs2 r₀ X j)
    · change ((symbolGroupEquiv (pairModel D).filtration (pairModel D).basis (pairWeight ω)
        (pairLayers hF) hs1 hs2).symm Y).fst ((pairIdx ω 1).symm (Sum.inr j)) =
        (r₁ : ℝ) * ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X).fst j
      rw [hYfst]
      have h3 := hY (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨1, j.1⟩)
      rw [h1, Equiv.symm_apply_apply] at h3
      exact h3.trans (single_dil_repr_fst hF hs1 hs2 r₁ X j)
  · funext u
    rcases u with j | j
    · change ((symbolGroupEquiv (pairModel D).filtration (pairModel D).basis (pairWeight ω)
        (pairLayers hF) hs1 hs2).symm Y).snd ((pairIdx ω 2).symm (Sum.inl j)) =
        (r₀ : ℝ) ^ 2 * ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X).snd j
      rw [hYsnd]
      have h3 := hY (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨0, j.1⟩)
      rw [h0, Equiv.symm_apply_apply] at h3
      exact h3.trans (single_dil_repr_snd hF hs1 hs2 r₀ X j)
    · change ((symbolGroupEquiv (pairModel D).filtration (pairModel D).basis (pairWeight ω)
        (pairLayers hF) hs1 hs2).symm Y).snd ((pairIdx ω 2).symm (Sum.inr j)) =
        (r₁ : ℝ) ^ 2 * ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X).snd j
      rw [hYsnd]
      have h3 := hY (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨1, j.1⟩)
      rw [h1, Equiv.symm_apply_apply] at h3
      exact h3.trans (single_dil_repr_snd hF hs1 hs2 r₁ X j)


end PairB5

/-- **The extrapolation step, type II, on the library's types.** Let `D` be a rational filtered
nilmanifold of degree `s ∈ {1, 2}` with an adapted basis of weights `ω` and `X` a symbol. If for
every pair `(ℓ, ℓ')` of a set `Γ ⊆ (L/2, L]²` of density `c` the symbol `Y (ℓ, ℓ')` of the pair
model `D × D`, whose coordinates are those of `(δ_{qℓ} X, δ_{qℓ'} X)`, has a
`ControlledSymbolFactorization` for the frequency `(η, -η)` at the box scale `A ≥ exp (C B³)`, then
the undilated `X` has an `ExtrapolatedSymbolFactorizationII` at the scale `A L / 2`. The complexity
of the pair model is `p` (`2 d ≤ p` and the structure constants have height `≤ p`). -/
theorem symbol_dilation_extrapolation_typeII_clone :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}, 1 ≤ s → s ≤ 2 →
      ∀ (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
        (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
        (η : L →ₗ[ℚ] ℚ) (p : ℝ), (2 * d : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (D.basis.repr ⁅D.basis i, D.basis j⁆ k) ≤ p) →
      ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.exp p →
      ∀ L' : ℕ, Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ L' →
      ∀ Γ : Finset (ℕ × ℕ),
        (∀ pr ∈ Γ, (L' : ℝ) / 2 < pr.1 ∧ (pr.1 : ℝ) ≤ L' ∧ (L' : ℝ) / 2 < pr.2 ∧
          (pr.2 : ℝ) ≤ L') →
      c * (L' : ℝ) ^ 2 ≤ Γ.card → ∀ A : ℝ, Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ A →
      ∀ X : D.filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1),
      ∀ Y : ℕ × ℕ → (pairModel D).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1),
      (∀ pr ∈ Γ, ∀ k : Fin (Fintype.card (Σ _ : Fin 2, Fin d)),
        ((pairAssoc D ω hF).baseChange ℝ).repr (Y pr).coord k =
          ((singleAssoc D ω hF).baseChange ℝ).repr
            (D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1)
              (if ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).1 = 0
                then ((q * pr.1 : ℕ) : ℚ) else ((q * pr.2 : ℕ) : ℚ)) X).coord
            ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).2) →
      (∀ pr ∈ Γ, (pairModel D).filtration.ControlledSymbolFactorization (pairModel D).basis
        (pairWeight ω) (pairLayers hF) (pairFreq η) (fun _ : Unit => A) (Y pr) p) →
      ExtrapolatedSymbolFactorizationII D.filtration D.basis ω hF η (A * L' / 2) X
        (C * (p + Real.log (1 / c) + 1) ^ 4) := by
  obtain ⟨C, hC⟩ := symbol_dilation_extrapolation_typeII
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro L _ _ s d hs1 hs2 D ω hF η p hd hc c hc0 hc1 q hq1 hq L' hL Γ hΓ hcard A hA X Y hY hfac
  have hB := step2Graded_associatedGraded D.filtration D.basis ω hF hs2
  have hBπ := step2Graded_associatedGraded (pairModel D).filtration (pairModel D).basis
    (pairWeight ω) (pairLayers hF) hs2
  have hp0 : 0 ≤ p := le_trans (by positivity) hd
  have hlam : 0 ≤ Real.log (1 / c) :=
    Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  have hd' : ((Fintype.card (Idx1 ω ⊕ Idx1 ω) + Fintype.card (Idx2 ω ⊕ Idx2 ω) : ℕ) : ℝ) ≤ p := by
    have h1 := card_split hB
    rw [Fintype.card_fin] at h1
    have h2 : Fintype.card (Idx1 ω ⊕ Idx1 ω) + Fintype.card (Idx2 ω ⊕ Idx2 ω) = 2 * d := by
      rw [Fintype.card_sum, Fintype.card_sum]
      omega
    rw [h2]
    push_cast
    exact hd
  have hc' : ∀ i j k, ratLogHeight ((stepTwoAlgebra (singleAssoc D ω hF) ω).c i j k) ≤ p := by
    intro i j k
    rw [single_c_eq hF]
    exact hc _ _ _
  have hex : ∀ pr : ℕ × ℕ,
      ∃ (Wc : LieSubalgebra ℚ (pairModel D).filtration.AssociatedGraded)
        (hW : BasisGradedSubmodule (pairAssoc D ω hF) (pairWeight ω) Wc.toSubmodule) (m : ℕ),
        pr ∈ Γ → ((m : ℝ) ≤ Real.exp p ∧
          (∀ x ∈ Wc, basisGradeProjection (pairAssoc D ω hF) (pairWeight ω) s x = x →
            (pairModel D).filtration.gradedFrequency (pairModel D).basis (pairWeight ω)
              (pairLayers hF) (pairFreq η) x = 0) ∧
          Datum p (toGraded hBπ Wc hW) A (Real.exp p) m
            ((symbolGroupEquiv (pairModel D).filtration (pairModel D).basis (pairWeight ω)
              (pairLayers hF) hs1 hs2).symm (Y pr))) := by
    intro pr
    by_cases hpr : pr ∈ Γ
    · obtain ⟨Wc, hW, m, h1, h2, h3⟩ := datum_of_controlledSymbolFactorization
        (pairModel D).filtration (pairModel D).basis (pairWeight ω) (pairLayers hF) hs1 hs2
        (pairFreq η) (hfac pr hpr)
      exact ⟨Wc, hW, m, fun _ => ⟨h1, h2, h3⟩⟩
    · refine ⟨⊥, fun j x hx => ?_, 0, fun h => absurd h hpr⟩
      have hx0 : x = 0 := by simpa using hx
      subst hx0
      simp
  choose Wc hW m hdat using hex
  have hD : ∀ pr ∈ Γ, Datum p
      (GradedSubalg.transport (pairEquiv hF) (toGraded hBπ (Wc pr) (hW pr))) A (Real.exp p)
      (m pr) (SymbolGroup.biDil ((q : ℝ) * pr.1) ((q : ℝ) * pr.2)
        ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X)) := by
    intro pr hpr
    have h1 := Datum.transport (pairEquiv hF) (hdat pr hpr).2.2
    rw [pair_map_eq_biDil hF hs1 hs2 ((q * pr.1 : ℕ) : ℚ) ((q * pr.2 : ℕ) : ℚ) X (Y pr)
      (hY pr hpr)] at h1
    have e1 : ((((q * pr.1 : ℕ) : ℚ)) : ℝ) = (q : ℝ) * pr.1 := by push_cast; ring
    have e2 : ((((q * pr.2 : ℕ) : ℚ)) : ℝ) = (q : ℝ) * pr.2 := by push_cast; ring
    rw [e1, e2] at h1
    exact h1
  have hkill : ∀ pr ∈ Γ, ∀ w ∈ (GradedSubalg.transport (pairEquiv hF)
      (toGraded hBπ (Wc pr) (hW pr))).toSubmodule, (s = 2 → w.1 = 0) → (s = 1 → w.2 = 0) →
      frPair (fun i : Idx1 ω => η (D.basis i.1)) w.1 +
        frPair (fun k : Idx2 ω => η (D.basis k.1)) w.2 = 0 := by
    intro pr hpr w hw h2 h1
    have hmem : (phi hBπ).symm ((pairEquiv hF).psi.symm w) ∈ Wc pr := hw
    rw [← pair_gradedFrequency hF hBπ η w]
    refine (hdat pr hpr).2.1 _ hmem (gradeProjection_top_eq hBπ hs1 hs2 _ (fun hs => ?_)
      (fun hs => ?_))
    · rw [LinearEquiv.apply_symm_apply]
      funext i
      change w.1 (pairIdx ω 1 i) = 0
      rw [h2 hs]
      rfl
    · rw [LinearEquiv.apply_symm_apply]
      funext i
      change w.2 (pairIdx ω 2 i) = 0
      rw [h1 hs]
      rfl
  have hemp : s = 1 → IsEmpty (Idx2 ω) := fun hs => ⟨fun k => by
    have h1 := D.filtration.adaptedBasis_weight_le_step D.basis ω hF k.1
    have h2 := k.2
    omega⟩
  have hW₂ : ∀ pr ∈ Γ, ∀ z, ((0 : Idx1 ω ⊕ Idx1 ω → ℚ), z) ∈ (GradedSubalg.transport
      (pairEquiv hF) (toGraded hBπ (Wc pr) (hW pr))).toSubmodule →
      frPair (fun k : Idx2 ω => η (D.basis k.1)) z = 0 := by
    intro pr hpr z hz
    rcases (by omega : s = 1 ∨ s = 2) with hs | hs
    · have := hemp hs
      simp [frPair_apply, frLin_apply]
    · have := hkill pr hpr _ hz (fun _ => rfl) (fun h => by omega)
      simpa using this
  have hW₁ : ∀ pr ∈ Γ, s = 1 → ∀ z, (z, (0 : Idx2 ω ⊕ Idx2 ω → ℚ)) ∈ (GradedSubalg.transport
      (pairEquiv hF) (toGraded hBπ (Wc pr) (hW pr))).toSubmodule →
      frPair (fun i : Idx1 ω => η (D.basis i.1)) z = 0 := by
    intro pr hpr hs z hz
    have := hkill pr hpr _ hz (fun h => by omega) (fun _ => rfl)
    simpa using this
  have hA' : Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ A :=
    le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith) 3))) hA
  have hL' : Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ L' :=
    le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith) 3))) hL
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
  have hL1 : (1 : ℝ) ≤ L' := le_trans (Real.one_le_exp (by positivity)) hL
  obtain ⟨pr, hpr, m', hm', -, hKdat⟩ := hC (stepTwoAlgebra (singleAssoc D ω hF) ω) p hd' hc'
    c hc0 hc1 q hq1 hq L' hL' Γ hΓ hcard A hA'
    ((symbolGroupEquiv D.filtration D.basis ω hF hs1 hs2).symm X)
    (fun pr => GradedSubalg.transport (pairEquiv hF) (toGraded hBπ (Wc pr) (hW pr))) m
    (fun pr hpr => ⟨(hdat pr hpr).1, hD pr hpr⟩)
  have hu1 : 1 ≤ p + Real.log (1 / c) + 1 := by linarith
  have hM : C * (p + Real.log (1 / c)) ^ 4 ≤ max C 1 * (p + Real.log (1 / c) + 1) ^ 4 := by
    calc C * (p + Real.log (1 / c)) ^ 4 ≤ max C 1 * (p + Real.log (1 / c)) ^ 4 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 1 * (p + Real.log (1 / c) + 1) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 4)
            (le_trans zero_le_one (le_max_right _ _))
  have hMe : Real.exp (C * (p + Real.log (1 / c)) ^ 4) ≤
      Real.exp (max C 1 * (p + Real.log (1 / c) + 1) ^ 4) := Real.exp_le_exp.mpr hM
  exact extrapolatedSymbolFactorizationII_of_datum D.filtration D.basis ω hF hs1 hs2 η
    ((GradedSubalg.transport (pairEquiv hF)
      (toGraded hBπ (Wc pr) (hW pr))).plusDerived.commonKernel)
    (GradedSubalg.derived_le_commonKernel _)
    (fun k hk k' hk' => commonKernel_flag _ _ (hW₂ pr hpr) hk hk')
    (fun _ hDf => commonKernel_layer₂_freq _ hDf _ (hW₂ pr hpr))
    (fun hs => commonKernel_layer₁_freq _ _ (hW₁ pr hpr hs))
    (p := C * (p + Real.log (1 / c)) ^ 4) (p' := max C 1 * (p + Real.log (1 / c) + 1) ^ 4)
    hM (by positivity) hMe (hm'.trans hMe) hKdat

end PrimeCarleson.Proof.Fplus31
