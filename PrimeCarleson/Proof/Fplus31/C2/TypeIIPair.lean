module

public import PrimeCarleson.Proof.Fplus31.C2.Symbol
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Product
public import OAI.Combinatorics.Progressions.Nilpotent.CommonProductNiltestFamily
public import OAI.Combinatorics.Progressions.Linear.TripleProductBasisBounds
public import OAI.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency

/-!
# The type II step, the pair model `D × D`: indices, structure constants, frequency, symbols

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
vendored library's `RationalFilteredNilmanifold.pi (fun _ : Fin 2 => D)` has the Lie algebra
`Fin 2 → L`, the basis `productFinBasis` indexed by `Fin (card (Σ _ : Fin 2, Fin d))` and the
weights `productBasisWeight`. This file collects what the type II chain needs about it:

* `pairIndexEquiv`, `pairWeight`, `pairIdx`: the index equivalence
  `Fin (card (Σ _ : Fin 2, Fin d)) ≃ Fin d ⊕ Fin d` and the induced equivalences of the weight-`n`
  indices (the layer-one and layer-two indices of `gr (D × D)` and of `gr D ⊕ gr D`);
* `pairBasis_lie_repr`, `pair_c_eq`: the structure constants of `gr (D × D)` are those of the block
  diagonal product `(gr D).prod` of `Extrapolation/Product.lean`, so that the data of the pair model
  transport to the abstract model of the abstract extrapolation (`C2/TypeIIAlg.lean`);
* `pairFreq`, `pairFreq_basis`: the frequency `(η, -η)` of the pair model (`piFrequency` of
  `![η, -η]`) in the pair basis;
* `orbitSymbol`, `orbitSymbol_repr`, `pair_orbitSymbol_repr`: the real coordinates of the symbol
  of a one-variable orbit, and the symbol of a product orbit `piRealOrbit` has as coordinates the
  coordinates of the symbols of the two factors.

-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module

section PairIndex

/-- `(Σ _ : Fin 2, Fin d) ≃ Fin d ⊕ Fin d`. -/
def sigmaFin2Equiv (d : ℕ) : (Σ _ : Fin 2, Fin d) ≃ Fin d ⊕ Fin d where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun y := Sum.elim (fun j => ⟨0, j⟩) (fun j => ⟨1, j⟩) y
  left_inv := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp
  right_inv := by
    rintro (j | j) <;> simp

/-- The index equivalence of the product basis of the pair model. -/
def pairIndexEquiv (d : ℕ) : Fin (Fintype.card (Σ _ : Fin 2, Fin d)) ≃ Fin d ⊕ Fin d :=
  (Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm.trans (sigmaFin2Equiv d)

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

/-- The pair model `D × D`. -/
abbrev pairModel : RationalFilteredNilmanifold (Fin 2 → L) s (Fintype.card (Σ _ : Fin 2, Fin d)) :=
  RationalFilteredNilmanifold.pi (fun _ : Fin 2 => D)

/-- The basis vectors of the pair model are the single-component vectors. -/
theorem pairBasis_apply (k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    (pairModel D).basis k =
      Pi.single ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).1
        (D.basis ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).2) := by
  change (RationalFilteredNilmanifold.productFinBasis (fun _ : Fin 2 => D)) k = _
  rw [RationalFilteredNilmanifold.productFinBasis, Basis.reindex_apply, Pi.basis_apply]



/-- The structure constants of the pair basis: those of `D` on the diagonal blocks. -/
theorem pairBasis_lie_repr (i j k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    (pairModel D).basis.repr ⁅(pairModel D).basis i, (pairModel D).basis j⁆ k =
      if ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm i).1 =
          ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm j).1 ∧
        ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm i).1 =
          ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).1 then
        D.basis.repr ⁅D.basis ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm i).2,
          D.basis ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm j).2⁆
          ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).2 else 0 := by
  classical
  rw [RationalFilteredNilmanifold.productFinBasis_repr]
  rw [pairBasis_apply, pairBasis_apply]
  generalize (Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm i = zi
  generalize (Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm j = zj
  generalize (Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k = zk
  obtain ⟨a, i'⟩ := zi
  obtain ⟨b, j'⟩ := zj
  obtain ⟨c, k'⟩ := zk
  dsimp only
  by_cases hac : c = a
  · subst c
    rw [lie_pi_apply, Pi.single_eq_same]
    by_cases hba : b = a
    · subst b
      rw [Pi.single_eq_same, ite_eq_left ⟨rfl, rfl⟩]
    · rw [Pi.single_eq_of_ne (Ne.symm hba), lie_zero, map_zero, Finsupp.zero_apply,
        ite_eq_right (fun h => hba h.1.symm)]
  · rw [lie_pi_apply, Pi.single_eq_of_ne hac, zero_lie, map_zero, Finsupp.zero_apply,
      ite_eq_right (fun h => hac h.2.symm)]

variable (ω : Fin d → ℕ)

/-- The weights of the pair basis. -/
abbrev pairWeight : Fin (Fintype.card (Σ _ : Fin 2, Fin d)) → ℕ :=
  RationalFilteredNilmanifold.productBasisWeight (d := fun _ : Fin 2 => d) (fun _ => ω)

/-- The pair weight of a basis vector is the weight of its component index. -/
theorem pairWeight_equivFin (a : Fin 2) (j : Fin d) :
    pairWeight ω (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨a, j⟩) = ω j := by
  simp [pairWeight, RationalFilteredNilmanifold.productBasisWeight]

/-- The index equivalence on the first block. -/
theorem pairIndexEquiv_equivFin_zero (j : Fin d) :
    pairIndexEquiv d (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨0, j⟩) = Sum.inl j := by
  simp [pairIndexEquiv, sigmaFin2Equiv]

/-- The index equivalence on the second block. -/
theorem pairIndexEquiv_equivFin_one (j : Fin d) :
    pairIndexEquiv d (Fintype.equivFin (Σ _ : Fin 2, Fin d) ⟨1, j⟩) = Sum.inr j := by
  simp [pairIndexEquiv, sigmaFin2Equiv]

/-- The weight of the pair basis in the coordinates `Fin d ⊕ Fin d`. -/
theorem pairWeight_eq (k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    pairWeight ω k = Sum.elim ω ω (pairIndexEquiv d k) := by
  obtain ⟨z, rfl⟩ := (Fintype.equivFin (Σ _ : Fin 2, Fin d)).surjective k
  obtain ⟨a, j⟩ := z
  rw [pairWeight_equivFin]
  have h2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases h2 a with rfl | rfl
  · rw [pairIndexEquiv_equivFin_zero]
    rfl
  · rw [pairIndexEquiv_equivFin_one]
    rfl

/-- The underlying sum of `Equiv.subtypeSum`. -/
theorem subtypeSum_val {α β : Type*} {p : α ⊕ β → Prop} (c : α ⊕ β) (h : p c) :
    Sum.map Subtype.val Subtype.val (Equiv.subtypeSum (p := p) ⟨c, h⟩) = c := by
  rcases c with a | a <;> rfl

/-- The index equivalence of the weight-`n` indices of the pair basis. -/
def pairIdx (n : ℕ) : {k : Fin (Fintype.card (Σ _ : Fin 2, Fin d)) // pairWeight ω k = n} ≃
    {i : Fin d // ω i = n} ⊕ {i : Fin d // ω i = n} :=
  (Equiv.subtypeEquiv (q := fun c : Fin d ⊕ Fin d => Sum.elim ω ω c = n) (pairIndexEquiv d)
    (fun k => by rw [pairWeight_eq])).trans (Equiv.subtypeSum (p := fun c => Sum.elim ω ω c = n))

/-- The index equivalence of the weight-`n` indices lies over `pairIndexEquiv`. -/
theorem pairIdx_val (n : ℕ)
    (k : {k : Fin (Fintype.card (Σ _ : Fin 2, Fin d)) // pairWeight ω k = n}) :
    Sum.map Subtype.val Subtype.val (pairIdx ω n k) = pairIndexEquiv d k.1 := by
  exact subtypeSum_val (p := fun c : Fin d ⊕ Fin d => Sum.elim ω ω c = n) (pairIndexEquiv d k.1) _


/-- An index in the first block corresponds to a pair `⟨0, j⟩`. -/
theorem sigma_of_inl {k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))} {j : Fin d}
    (h : pairIndexEquiv d k = Sum.inl j) :
    (Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k = ⟨0, j⟩ := by
  have h2 : (sigmaFin2Equiv d).symm (pairIndexEquiv d k) =
      (Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k := (sigmaFin2Equiv d).symm_apply_apply _
  rw [h] at h2
  exact h2.symm

/-- An index in the second block corresponds to a pair `⟨1, j⟩`. -/
theorem sigma_of_inr {k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))} {j : Fin d}
    (h : pairIndexEquiv d k = Sum.inr j) :
    (Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k = ⟨1, j⟩ := by
  have h2 : (sigmaFin2Equiv d).symm (pairIndexEquiv d k) =
      (Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k := (sigmaFin2Equiv d).symm_apply_apply _
  rw [h] at h2
  exact h2.symm

variable {D} {ω} (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

include hF in
/-- The pair basis is adapted to the product filtration with the product weights. -/
theorem pairLayers (j : ℕ) :
    (pairModel D).filtration.layer j =
      Submodule.span ℚ ((pairModel D).basis '' {k | j ≤ pairWeight ω k}) :=
  RationalFilteredNilmanifold.pi_layer_span (fun _ : Fin 2 => D) (fun _ => ω)
    (fun _ n => hF n) j

variable (D ω) in
/-- The associated graded basis of the pair model. -/
abbrev pairAssoc (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})) :=
  (pairModel D).filtration.associatedGradedBasis (pairModel D).basis (pairWeight ω)
    (pairLayers hF)

variable (D ω) in
/-- The associated graded basis of the single model. -/
abbrev singleAssoc (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})) :=
  D.filtration.associatedGradedBasis D.basis ω hF

/-- The structure constants of `gr D` in the weight-one and weight-two indices. -/
theorem single_c_eq (i j : {k : Fin d // ω k = 1}) (k : {k : Fin d // ω k = 2}) :
    (stepTwoAlgebra (singleAssoc D ω hF) ω).c i j k =
      D.basis.repr ⁅D.basis i.1, D.basis j.1⁆ k.1 := by
  change (singleAssoc D ω hF).repr ⁅singleAssoc D ω hF i.1, singleAssoc D ω hF j.1⁆ k.1 = _
  rw [NilpotentLieFiltration.associatedGradedBasis_bracket,
    ite_eq_left (by have := i.2; have := j.2; have := k.2; omega)]

/-- **The structure constants of `gr (D × D)` are those of the product `gr D × gr D`.** -/
theorem pair_c_eq (i j : {k : Fin (Fintype.card (Σ _ : Fin 2, Fin d)) // pairWeight ω k = 1})
    (k : {k : Fin (Fintype.card (Σ _ : Fin 2, Fin d)) // pairWeight ω k = 2}) :
    (stepTwoAlgebra (pairAssoc D ω hF) (pairWeight ω)).c i j k =
      (stepTwoAlgebra (singleAssoc D ω hF) ω).prod.c (pairIdx ω 1 i) (pairIdx ω 1 j)
        (pairIdx ω 2 k) := by
  change (pairAssoc D ω hF).repr ⁅pairAssoc D ω hF i.1, pairAssoc D ω hF j.1⁆ k.1 = _
  rw [NilpotentLieFiltration.associatedGradedBasis_bracket, pairBasis_lie_repr]
  have hi := pairIdx_val ω 1 i
  have hj := pairIdx_val ω 1 j
  have hk := pairIdx_val ω 2 k
  have e1 := i.2
  have e2 := j.2
  have e3 := k.2
  rw [ite_eq_left (by omega : pairWeight ω i.1 + pairWeight ω j.1 = pairWeight ω k.1)]
  rcases hu : pairIdx ω 1 i with i' | i' <;> rcases hv : pairIdx ω 1 j with j' | j' <;>
    rcases hw : pairIdx ω 2 k with k' | k' <;> rw [hu] at hi <;> rw [hv] at hj <;>
    rw [hw] at hk <;> simp only [Sum.map_inl, Sum.map_inr] at hi hj hk
  all_goals (first | rw [sigma_of_inl hi.symm] | rw [sigma_of_inr hi.symm])
  all_goals (first | rw [sigma_of_inl hj.symm] | rw [sigma_of_inr hj.symm])
  all_goals (first | rw [sigma_of_inl hk.symm] | rw [sigma_of_inr hk.symm])
  all_goals simp [Step2Algebra.prod, single_c_eq]


/-- The pair frequency `(η, -η)`. -/
def pairFreq (η : L →ₗ[ℚ] ℚ) : (Fin 2 → L) →ₗ[ℚ] ℚ :=
  piFrequency (fun i : Fin 2 => if i = 0 then η else -η)

/-- The pair frequency on the pair basis. -/
theorem pairFreq_basis (η : L →ₗ[ℚ] ℚ) (k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    pairFreq η ((pairModel D).basis k) =
      Sum.elim (fun j => η (D.basis j)) (fun j => -η (D.basis j)) (pairIndexEquiv d k) := by
  obtain ⟨z, rfl⟩ := (Fintype.equivFin (Σ _ : Fin 2, Fin d)).surjective k
  obtain ⟨a, j⟩ := z
  have h2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  unfold pairFreq
  rw [RationalFilteredNilmanifold.piFrequency_basis]
  rcases h2 a with rfl | rfl
  · rw [pairIndexEquiv_equivFin_zero]
    simp
  · rw [pairIndexEquiv_equivFin_one]
    simp

end PairIndex

section SymbolCoord

open VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

/-- The symbol of a one-variable polynomial orbit. -/
def orbitSymbol (g : F.realification.PolynomialOrbit (fun _ : Unit => 1)) :
    F.RealPolynomialSymbolGroup (fun _ : Unit => 1) :=
  F.realPolynomialSymbolHom b ω hF (fun _ : Unit => 1) ⟨⟨g.log, g.property⟩⟩

/-- The coordinates of the symbol of an orbit: the `ω i`-th coefficient of the log polynomial. -/
theorem orbitSymbol_repr (g : F.realification.PolynomialOrbit (fun _ : Unit => 1)) (i : ι) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr (orbitSymbol F b ω hF g).coord i =
      (b.baseChange ℝ).repr (coefficients g.log (unitMonomial (ω i))) i := by
  rw [assocBasisR_repr F b ω hF]
  exact F.realSymbolOfPolynomial_coordinate b ω hF (fun _ : Unit => 1) g.log
    ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩

end SymbolCoord


section PairSymbol

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

/-- The real coordinates of the pair basis are the coordinates of the matching component. -/
theorem pairBasisR_repr (y : ℝ ⊗[ℚ] (Fin 2 → L)) (k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    ((pairModel D).basis.baseChange ℝ).repr y k =
      (D.basis.baseChange ℝ).repr
        (realificationLieHom (liePiEval (R := ℚ) (M := fun _ : Fin 2 => L)
          ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).1) y)
        ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).2 := by
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    rw [Module.Basis.baseChange_repr_tmul, realificationLieHom_tmul,
      Module.Basis.baseChange_repr_tmul]
    congr 1
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]


variable {D} {ω : Fin d → ℕ}
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

include hF in
/-- **The symbol of a product orbit has the symbols of the factors as coordinates.** -/
theorem pair_orbitSymbol_repr
    (g : Fin 2 → D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    ((pairAssoc D ω hF).baseChange ℝ).repr
      (orbitSymbol (pairModel D).filtration (pairModel D).basis (pairWeight ω) (pairLayers hF)
        (NilpotentLieFiltration.piRealOrbit (fun _ : Fin 2 => D.filtration) g)).coord k =
    ((singleAssoc D ω hF).baseChange ℝ).repr
      (orbitSymbol D.filtration D.basis ω hF
        (g ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).1)).coord
      ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).2 := by
  have h1 := orbitSymbol_repr (pairModel D).filtration (pairModel D).basis (pairWeight ω)
    (pairLayers hF) (NilpotentLieFiltration.piRealOrbit (fun _ : Fin 2 => D.filtration) g) k
  have h2 := orbitSymbol_repr D.filtration D.basis ω hF
    (g ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).1)
    ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).2
  have h3 := NilpotentLieFiltration.piRealOrbit_coefficient (fun _ : Fin 2 => D.filtration) g
    (unitMonomial (pairWeight ω k)) ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).1
  exact h1.trans ((pairBasisR_repr D _ k).trans
    ((congrArg (fun y => (D.basis.baseChange ℝ).repr y
      ((Fintype.equivFin (Σ _ : Fin 2, Fin d)).symm k).2) h3).trans h2.symm))

end PairSymbol

end PrimeCarleson.Proof.Fplus31
