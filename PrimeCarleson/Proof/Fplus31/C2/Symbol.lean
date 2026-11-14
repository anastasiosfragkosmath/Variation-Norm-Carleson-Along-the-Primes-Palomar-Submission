module

public import PrimeCarleson.Proof.Fplus31.C2.Dictionary
public import PrimeCarleson.Proof.Fplus31.G1.Compose

/-!
# The extrapolation step on the library's types: the symbol of a one-variable niltest

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
dictionary `C2/Dictionary.lean` identifies the abstract objects of the abstract extrapolation
(`Extrapolation/`) with the real BCH group and the basis-graded Lie subalgebras of a weighted
`ℚ`-Lie algebra. Here the Lie algebra is the vendored library's `gr L = F.AssociatedGraded` with the
basis `F.associatedGradedBasis b ω hF` (weights `ω ∈ {1, 2}`, filtration degree `s ∈ {1, 2}`), and
the real BCH group is the vendored library's `F.RealPolynomialSymbolGroup (fun _ : Unit => 1)`.

* `step2Graded_associatedGraded`: `(gr L, associatedGradedBasis, ω)` is `Step2Graded`; its
  structure constants are `b.repr ⁅b i, b j⁆ k` when the weights add up and `0` otherwise, so they
  have height `≤ p` as soon as the structure constants of `b` have (the complexity budget `p` of
  `GeometryComplexityLE`);
* `symbolSlowBound_iff`, `symbolRationalGrid_iff`: `SymbolSlowBound` and `SymbolRationalGrid` in
  the basis `associatedGradedBasis` (`|coordinate i| ≤ M / A ^ ω i`, `m * coordinate i ∈ ℤ`);
* `symbolGroupEquiv`, `symbolGroupEquiv_dil`: the isomorphism
  `SymbolGroup ≃* RealPolynomialSymbolGroup` and the compatibility of the dilations `δ_r` with
  `realPolynomialSymbolDilationHom`;
* `ExtrapolatedSymbolFactorization`: the output type, a factorization of the undilated symbol
  relative to `K = W + [gr, gr]`, with `W` exposed;
* `datum_of_controlledSymbolFactorization`, `extrapolatedSymbolFactorization_of_datum`: the two
  translations between the vendored library's `ControlledSymbolFactorization` and the abstract
  `Datum`;
* `symbol_dilation_extrapolation_clone`: the extrapolation step on the library's types;
* `lie_mem_of_mem_plusCommutator`, `gradedFrequency_lie_eq_zero`: for the iteration, `⁅K₁, K₁⁆ ⊆ W`
  and `η ⁅K₁, K₁⁆ = 0`.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section Clone

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

/-- The associated graded Lie algebra of a filtration of degree `s ≤ 2` with an adapted basis is a
`Step2Graded` basis: weights `1` and `2`, brackets add weights. -/
theorem step2Graded_associatedGraded (hs2 : s ≤ 2) :
    Step2Graded (F.associatedGradedBasis b ω hF) ω where
  weight i := by
    have h1 := F.adaptedBasis_weight_pos b ω hF i
    have h2 := F.adaptedBasis_weight_le_step b ω hF i
    omega
  bracket i j k h := by
    rw [F.associatedGradedBasis_bracket b ω hF] at h
    by_contra hne
    exact h (ite_eq_right hne)

/-- The coordinates in the real basis `associatedGradedBasis ⊗ ℝ` are those of the vendored
library's real symbol basis `polynomialSymbolBasis ⊗ ℝ` at the monomial `unitMonomial (ω i)`. -/
theorem assocBasisR_repr (y : ℝ ⊗[ℚ] F.AssociatedGraded) (i : ι) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr y i =
      ((F.polynomialSymbolBasis b ω hF (fun _ : Unit => 1)).baseChange ℝ).repr y
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    rw [Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      F.associatedGradedBasis_repr]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- A symbol basis index of a one-variable symbol is a pure power. -/
theorem symbolIndex_fst (z : NilpotentLieFiltration.SymbolBasisIndex (fun _ : Unit => 1) ω) :
    z.val.1 = unitMonomial (ω z.val.2) := by
  have := unitMonomial_weight z.val.1
  rw [z.property] at this
  exact this.symm

/-- A symbol basis index of a one-variable symbol is determined by its basis vector. -/
theorem symbolIndex_eq (z : NilpotentLieFiltration.SymbolBasisIndex (fun _ : Unit => 1) ω) :
    z = ⟨(unitMonomial (ω z.val.2), z.val.2), weight_unitMonomial _⟩ :=
  Subtype.ext (Prod.ext (symbolIndex_fst ω z) rfl)

/-- The monomial scale of a pure power in one variable. -/
theorem monomialScale_unit (A : ℝ) (n : ℕ) :
    monomialScale (fun _ : Unit => A) (unitMonomial n) = A ^ n := by
  simp [monomialScale, unitMonomial, Finsupp.prod_single_index]

/-- The coordinates of the real symbol basis at `z` are the coordinates of
`associatedGradedBasis ⊗ ℝ` at `z.2`. -/
theorem polyRepr_eq (y : ℝ ⊗[ℚ] F.AssociatedGraded)
    (z : NilpotentLieFiltration.SymbolBasisIndex (fun _ : Unit => 1) ω) :
    ((F.polynomialSymbolBasis b ω hF (fun _ : Unit => 1)).baseChange ℝ).repr y z =
      ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr y z.val.2 := by
  rw [assocBasisR_repr, ← symbolIndex_eq]

/-- `SymbolSlowBound` for a one-variable symbol: the coordinate `i` is at most
`M / A ^ ω i`. -/
theorem symbolSlowBound_iff (A M : ℝ) (g : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)) :
    F.SymbolSlowBound b ω hF (fun _ => 1) (fun _ : Unit => A) M g ↔
      ∀ i, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr g.coord i| ≤ M / A ^ ω i := by
  constructor
  · intro h i
    have := h ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩
    rwa [monomialScale_unit, ← assocBasisR_repr] at this
  · intro h z
    have h1 := h z.val.2
    rw [← polyRepr_eq F b ω hF] at h1
    rw [symbolIndex_fst ω z, monomialScale_unit]
    exact h1

/-- `SymbolRationalGrid` for a one-variable symbol: `m` times every coordinate is an integer. -/
theorem symbolRationalGrid_iff (m : ℕ) (g : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)) :
    F.SymbolRationalGrid b ω hF (fun _ => 1) m g ↔
      ∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) *
        ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr g.coord i := by
  constructor
  · rintro ⟨k, hk⟩ i
    have h1 : ((k ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ : ℤ) : ℝ) =
        (m : ℝ) • ((F.polynomialSymbolBasis b ω hF (fun _ : Unit => 1)).baseChange ℝ).repr g.coord
          ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ :=
      congrFun hk _
    refine ⟨_, h1.trans ?_⟩
    rw [← assocBasisR_repr, smul_eq_mul]
  · intro h
    choose kk hkk using h
    refine ⟨fun z => kk z.val.2, funext fun z => ?_⟩
    change ((kk z.val.2 : ℤ) : ℝ) = (m : ℝ) • _
    rw [hkk, smul_eq_mul]
    exact congrArg (fun t => (m : ℝ) * t) (polyRepr_eq F b ω hF g.coord z).symm

end Clone

section Equiv

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
/-- The isomorphism of the abstract symbol group with the vendored library's real symbol group. -/
def symbolGroupEquiv (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    SymbolGroup (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω) ≃*
      F.RealPolynomialSymbolGroup (fun _ : Unit => 1) :=
  groupEquiv (step2Graded_associatedGraded F b ω hF hs2) hs1 hs2
    (F.polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : Unit => 1))

/-- The grading dilation of the abstract symbol group is the vendored library's
`realPolynomialSymbolDilationHom`. -/
theorem symbolGroupEquiv_dil (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (r : ℚ)
    (x : SymbolGroup (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω)) :
    symbolGroupEquiv F b ω hF hs1 hs2 (SymbolGroup.dil (r : ℝ) x) =
      F.realPolynomialSymbolDilationHom (fun _ : Unit => 1) r
        (symbolGroupEquiv F b ω hF hs1 hs2 x) := by
  apply NilpotentLieBCHGroup.ext
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  have h1 := repr_groupEquiv_dil (step2Graded_associatedGraded F b ω hF hs2) hs1 hs2
    (F.polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : Unit => 1)) (r : ℝ) x i
  change ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
    (groupEquiv (step2Graded_associatedGraded F b ω hF hs2) hs1 hs2
      (F.polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : Unit => 1))
        (SymbolGroup.dil (r : ℝ) x)).coord i = _ at h1 ⊢
  rw [h1]
  change _ = ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
    (F.realPolynomialSymbolDilation (fun _ : Unit => 1) r
      (symbolGroupEquiv F b ω hF hs1 hs2 x).coord) i
  rw [assocBasisR_repr F b ω hF (F.realPolynomialSymbolDilation (fun _ : Unit => 1) r
      (symbolGroupEquiv F b ω hF hs1 hs2 x).coord) i,
    F.realPolynomialSymbolDilation_repr b ω hF, weight_unitMonomial,
    assocBasisR_repr F b ω hF (groupEquiv (step2Graded_associatedGraded F b ω hF hs2) hs1 hs2
      (F.polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : Unit => 1)) x).coord i]
  rfl

/-- **A factorization of the undilated symbol relative to `K = W + [gr, gr]`** (the output of the
extrapolation step, in the vendored library's types): `X = E P R` with `E` slow at scale `T`, `R`
rational of denominator `m`, and `P ∈ exp (K_ℝ)` where `K = W + [gr, gr]` is a basis-graded Lie
subalgebra spanned by vectors of height `≤ p`, and `W` is a basis-graded Lie subalgebra whose top
layer is killed by `η`. The budget `p` bounds `log m`, `log` of the slow constant and the heights.
-/
def ExtrapolatedSymbolFactorization (η : L →ₗ[ℚ] ℚ) (T : ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)) (p : ℝ) : Prop :=
  ∃ (m : ℕ) (E P R : F.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (W K : LieSubalgebra ℚ F.AssociatedGraded) (v : ι → F.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ E * P * R = X ∧
    F.SymbolSlowBound b ω hF (fun _ => 1) (fun _ : Unit => T) (Real.exp p) E ∧
    F.SymbolRationalGrid b ω hF (fun _ => 1) m R ∧
    Submodule.span ℚ (Set.range v) = K.toSubmodule ∧
    BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω K.toSubmodule ∧
    (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v i) j) ≤ p) ∧
    BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) ∧
    K.toSubmodule = W.toSubmodule ⊔ commutatorSubmodule F.AssociatedGraded ∧
    P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) K)

/-- A `ControlledSymbolFactorization` at box scale `A` of a symbol `Y` gives the datum
`(W; A, e^p, m)` of the abstract model for `e⁻¹ Y`. -/
theorem datum_of_controlledSymbolFactorization (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ)
    {A p : ℝ} {Y : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)}
    (h : F.ControlledSymbolFactorization b ω hF η (fun _ : Unit => A) Y p) :
    ∃ (Wc : LieSubalgebra ℚ F.AssociatedGraded)
      (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω Wc.toSubmodule) (m : ℕ),
      (m : ℝ) ≤ Real.exp p ∧
      (∀ x ∈ Wc, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
        F.gradedFrequency b ω hF η x = 0) ∧
      Datum p (toGraded (step2Graded_associatedGraded F b ω hF hs2) Wc hW) A (Real.exp p) m
        ((symbolGroupEquiv F b ω hF hs1 hs2).symm Y) := by
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hh, hη, hP⟩ := h
  have hB := step2Graded_associatedGraded F b ω hF hs2
  refine ⟨W, hW, m, hmp, hη, ?_⟩
  have hE' := (symbolSlowBound_iff F b ω hF A (Real.exp p) E).mp hE
  have hR' := (symbolRationalGrid_iff F b ω hF m R).mp hR
  rw [symbolPointwiseSubalgebra_unit F b ω hF W hW] at hP
  have hP' : P.coord ∈ W.toSubmodule.baseChange ℝ := hP
  refine ⟨(gen_iff hB _ W.toSubmodule rfl p).mpr ⟨v, hv, hh⟩, hm,
    (symbolGroupEquiv F b ω hF hs1 hs2).symm E, (symbolGroupEquiv F b ω hF hs1 hs2).symm P,
    (symbolGroupEquiv F b ω hF hs1 hs2).symm R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod]
  · intro i
    have := hE' i.1
    rwa [i.2, pow_one] at this
  · intro k
    have := hE' k.1
    rwa [k.2] at this
  · exact fun i => hR' i.1
  · exact fun k => hR' k.1
  · exact (mem_baseChange_iff hB W.toSubmodule P.coord).mp hP'

/-- A datum for `W + D` of the abstract model gives an `ExtrapolatedSymbolFactorization`. -/
theorem extrapolatedSymbolFactorization_of_datum (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ)
    (Wc : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω Wc.toSubmodule)
    (hη : ∀ x ∈ Wc, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0)
    {T p p' M : ℝ} (hp : p ≤ p') (hT : 0 < T) (hM : M ≤ Real.exp p') {m : ℕ}
    (hm : (m : ℝ) ≤ Real.exp p') {X : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)}
    (h : Datum p (toGraded (step2Graded_associatedGraded F b ω hF hs2) Wc hW).plusDerived T M m
      ((symbolGroupEquiv F b ω hF hs1 hs2).symm X)) :
    ExtrapolatedSymbolFactorization F b ω hF η T X p' := by
  have hB := step2Graded_associatedGraded F b ω hF hs2
  obtain ⟨hgen, hm0, E, P, R, hprod, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨v, hv, hh⟩ := (gen_iff hB _ (ofGraded hB (toGraded hB Wc hW).plusDerived).toSubmodule
    (toSubmodule_eq_comap_ofGraded hB _) p).mp hgen
  have hMT : M / T ≤ Real.exp p' / T := div_le_div_of_nonneg_right hM hT.le
  have hMT2 : M / T ^ 2 ≤ Real.exp p' / T ^ 2 :=
    div_le_div_of_nonneg_right hM (by positivity)
  have hKgraded := basisGraded_ofGraded hB (toGraded hB Wc hW).plusDerived
  have kE1 : ∀ (Z : SymbolGroup (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω))
      (i : Idx1 ω), ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (symbolGroupEquiv F b ω hF hs1 hs2 Z).coord i.1 = Z.fst i :=
    fun Z i => repr_realElt_fst _ ω Z i
  have kE2 : ∀ (Z : SymbolGroup (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω))
      (k : Idx2 ω), ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (symbolGroupEquiv F b ω hF hs1 hs2 Z).coord k.1 = Z.snd k :=
    fun Z k => repr_realElt_snd _ ω Z k
  refine ⟨m, symbolGroupEquiv F b ω hF hs1 hs2 E, symbolGroupEquiv F b ω hF hs1 hs2 P,
    symbolGroupEquiv F b ω hF hs1 hs2 R, Wc, ofGraded hB (toGraded hB Wc hW).plusDerived, v,
    hm0, hm, ?_, ?_, ?_, hv, hKgraded, fun i j => (hh i j).trans hp, hW, hη, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod, MulEquiv.apply_symm_apply]
  · rw [symbolSlowBound_iff]
    refine (forall_idx hB).mpr ⟨fun i => ?_, fun k => ?_⟩
    · rw [kE1, i.2, pow_one]
      exact (h1 i).trans hMT
    · rw [kE2, k.2]
      exact (h2 k).trans hMT2
  · rw [symbolRationalGrid_iff]
    refine (forall_idx hB).mpr ⟨fun i => ?_, fun k => ?_⟩
    · rw [kE1]
      exact h3 i
    · rw [kE2]
      exact h4 k
  · exact Submodule.ext fun z => mem_ofGraded_plusDerived hB Wc hW z
  · rw [symbolPointwiseSubalgebra_unit F b ω hF _ hKgraded]
    change (symbolGroupEquiv F b ω hF hs1 hs2 P).coord ∈
      (ofGraded hB (toGraded hB Wc hW).plusDerived).toSubmodule.baseChange ℝ
    rw [mem_baseChange_iff hB, ← toSubmodule_eq_comap_ofGraded hB]
    change ((symbolOf _ ω (realElt _ ω P)).fst, (symbolOf _ ω (realElt _ ω P)).snd) ∈ _
    rw [symbolOf_realElt]
    exact h5

end Equiv

/-- **The extrapolation step on the library's types.** If for each `ℓ ∈ Λ` (`c L` many
`ℓ ∈ (L/2, L]`) the dilated symbol `δ_{qℓ} X` has a `ControlledSymbolFactorization` at the box scale
`A ≥ exp (C (p + log (1/c)) ^ 3)`, with complexity `p` (`dim ≤ p`, structure constants of height
`≤ p`), then the undilated `X` has an `ExtrapolatedSymbolFactorization` at the scale `A L / 2` of
complexity `C (p + log (1/c) + 1) ^ 4`, relative to `K = W + [gr, gr]` with `W` one of the `W_ℓ`.
The degree is `s ∈ {1, 2}` (`s = 1` is the abelian stage). -/
theorem symbol_dilation_extrapolation_clone :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ},
      1 ≤ s → s ≤ 2 →
      ∀ (F : NilpotentLieFiltration L s) (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (η : L →ₗ[ℚ] ℚ) (p : ℝ),
      (Fintype.card ι : ℝ) ≤ p → (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.exp p →
      ∀ L' : ℕ, 1 ≤ L' → ∀ Λ : Finset ℕ, (∀ ℓ ∈ Λ, (L' : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L') →
      c * L' ≤ Λ.card → ∀ A : ℝ, Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ A →
      ∀ X : F.RealPolynomialSymbolGroup (fun _ : Unit => 1),
      (∀ ℓ ∈ Λ, F.ControlledSymbolFactorization b ω hF η (fun _ : Unit => A)
        (F.realPolynomialSymbolDilationHom (fun _ : Unit => 1) (((q * ℓ : ℕ) : ℚ)) X) p) →
      ExtrapolatedSymbolFactorization F b ω hF η (A * L' / 2) X
        (C * (p + Real.log (1 / c) + 1) ^ 4) := by
  obtain ⟨C, hC⟩ := symbol_dilation_extrapolation
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro ι L _ _ _ s hs1 hs2 F b ω hF η p hd hc c hc0 hc1 q hq1 hq L' hL1 Λ hΛ hcard A hA X hfac
  have hB := step2Graded_associatedGraded F b ω hF hs2
  have hp0 : 0 ≤ p := le_trans (Nat.cast_nonneg _) hd
  have hlam : 0 ≤ Real.log (1 / c) :=
    Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  have hd' : ((Fintype.card (Idx1 ω) + Fintype.card (Idx2 ω) : ℕ) : ℝ) ≤ p := by
    rw [← card_split hB]
    exact hd
  have hc' : ∀ i j k, ratLogHeight ((stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω).c i j k)
      ≤ p := by
    intro i j k
    change ratLogHeight ((F.associatedGradedBasis b ω hF).repr
      ⁅F.associatedGradedBasis b ω hF i.1, F.associatedGradedBasis b ω hF j.1⁆ k.1) ≤ p
    rw [F.associatedGradedBasis_bracket b ω hF]
    by_cases h : ω i.1 + ω j.1 = ω k.1
    · rw [ite_eq_left h]
      exact hc _ _ _
    · rw [ite_eq_right h, ratLogHeight_zero]
      exact hp0
  have hex : ∀ ℓ : ℕ, ∃ (Wc : LieSubalgebra ℚ F.AssociatedGraded)
      (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω Wc.toSubmodule) (m : ℕ),
      ℓ ∈ Λ → ((m : ℝ) ≤ Real.exp p ∧
        (∀ x ∈ Wc, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
          F.gradedFrequency b ω hF η x = 0) ∧
        Datum p (toGraded hB Wc hW) A (Real.exp p) m ((symbolGroupEquiv F b ω hF hs1 hs2).symm
          (F.realPolynomialSymbolDilationHom (fun _ : Unit => 1) (((q * ℓ : ℕ) : ℚ)) X))) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ Λ
    · obtain ⟨Wc, hW, m, h1, h2, h3⟩ :=
        datum_of_controlledSymbolFactorization F b ω hF hs1 hs2 η (hfac ℓ hℓ)
      exact ⟨Wc, hW, m, fun _ => ⟨h1, h2, h3⟩⟩
    · refine ⟨⊥, fun j x hx => ?_, 0, fun h => absurd h hℓ⟩
      have hx0 : x = 0 := by simpa using hx
      subst hx0
      simp
  choose Wc hW m hdat using hex
  have hdil : ∀ ℓ : ℕ, (symbolGroupEquiv F b ω hF hs1 hs2).symm
      (F.realPolynomialSymbolDilationHom (fun _ : Unit => 1) (((q * ℓ : ℕ) : ℚ)) X) =
      SymbolGroup.dil ((q : ℝ) * ℓ) ((symbolGroupEquiv F b ω hF hs1 hs2).symm X) := by
    intro ℓ
    apply (symbolGroupEquiv F b ω hF hs1 hs2).injective
    rw [MulEquiv.apply_symm_apply]
    have hcast : ((((q * ℓ : ℕ) : ℚ)) : ℝ) = (q : ℝ) * ℓ := by push_cast; ring
    have := symbolGroupEquiv_dil F b ω hF hs1 hs2 (((q * ℓ : ℕ) : ℚ))
      ((symbolGroupEquiv F b ω hF hs1 hs2).symm X)
    rw [MulEquiv.apply_symm_apply, hcast] at this
    exact this.symm
  have hA' : Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ A :=
    le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith) 3))) hA
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
  obtain ⟨ℓ, hℓ, m', hm', -, hD⟩ := hC (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω) p hd'
    hc' c hc0 hc1 q hq1 hq L' hL1 Λ hΛ hcard A hA'
    ((symbolGroupEquiv F b ω hF hs1 hs2).symm X) (fun ℓ => toGraded hB (Wc ℓ) (hW ℓ)) m
    (fun ℓ hℓ => ⟨(hdat ℓ hℓ).1, by rw [← hdil]; exact (hdat ℓ hℓ).2.2⟩)
  have hu1 : 1 ≤ p + Real.log (1 / c) + 1 := by linarith
  have hu4 : p + Real.log (1 / c) + 1 ≤ (p + Real.log (1 / c) + 1) ^ 4 := by
    calc p + Real.log (1 / c) + 1 = (p + Real.log (1 / c) + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hu1 (by norm_num)
  have hCm : (p + Real.log (1 / c) + 1) ^ 4 ≤ max C 1 * (p + Real.log (1 / c) + 1) ^ 4 :=
    le_mul_of_one_le_left (by positivity) (le_max_right _ _)
  have hM : C * (p + Real.log (1 / c)) ^ 4 ≤ max C 1 * (p + Real.log (1 / c) + 1) ^ 4 := by
    calc C * (p + Real.log (1 / c)) ^ 4 ≤ max C 1 * (p + Real.log (1 / c)) ^ 4 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 1 * (p + Real.log (1 / c) + 1) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 4)
            (le_trans zero_le_one (le_max_right _ _))
  have hMe : Real.exp (C * (p + Real.log (1 / c)) ^ 4) ≤
      Real.exp (max C 1 * (p + Real.log (1 / c) + 1) ^ 4) := Real.exp_le_exp.mpr hM
  exact extrapolatedSymbolFactorization_of_datum F b ω hF hs1 hs2 η (Wc ℓ) (hW ℓ)
    (hdat ℓ hℓ).2.1 (p := p) (p' := max C 1 * (p + Real.log (1 / c) + 1) ^ 4)
    (by linarith) (by positivity) hMe (hm'.trans hMe) hD

section Stage

open Module

variable {ι L : Type*} [Finite ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

/-- **`K₁ = W₁`, hence `⁅K₁, K₁⁆ ⊆ W`.** If `K = W + [gr, gr]` and `W` is basis-graded, then two
elements of `K` of weight one lie in `W`, and so does their bracket (that is,
`β(K₁, K₁) = β(W₁, W₁) ⊆ W₂`, used by the descending stage of the iteration). -/
theorem lie_mem_of_mem_plusCommutator (hs2 : s ≤ 2)
    {W K : LieSubalgebra ℚ F.AssociatedGraded}
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hK : K.toSubmodule = W.toSubmodule ⊔ commutatorSubmodule F.AssociatedGraded)
    {x y : F.AssociatedGraded} (hx : x ∈ K) (hy : y ∈ K)
    (hx1 : basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 x = x)
    (hy1 : basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 y = y) : ⁅x, y⁆ ∈ W := by
  have hB := step2Graded_associatedGraded F b ω hF hs2
  have key : ∀ z ∈ K, basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 z = z →
      z ∈ W := by
    intro z hz hz1
    have hz' : z ∈ K.toSubmodule := hz
    rw [hK] at hz'
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hz'
    rw [map_add, gradeProjection_one_of_mem_commutator hB hc, add_zero] at hz1
    rw [← hz1]
    exact hW 1 w hw
  exact W.lie_mem (key x hx hx1) (key y hy hy1)

/-- **The flag.**  For `x, y ∈ K` of weight one, `η ⁅x, y⁆ = 0`, because `⁅x, y⁆ ∈ W` lies in the
top layer and `η` kills the top layer of `W`. -/
theorem gradedFrequency_lie_eq_zero (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ)
    {W K : LieSubalgebra ℚ F.AssociatedGraded}
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0)
    (hK : K.toSubmodule = W.toSubmodule ⊔ commutatorSubmodule F.AssociatedGraded)
    {x y : F.AssociatedGraded} (hx : x ∈ K) (hy : y ∈ K)
    (hx1 : basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 x = x)
    (hy1 : basisGradeProjection (F.associatedGradedBasis b ω hF) ω 1 y = y) :
    F.gradedFrequency b ω hF η ⁅x, y⁆ = 0 :=
  hη _ (lie_mem_of_mem_plusCommutator F b ω hF hs2 hW hK hx hy hx1 hy1)
    (gradeProjection_lie_top (step2Graded_associatedGraded F b ω hF hs2) hs1 hs2
      (F.adaptedBasis_weight_le_step b ω hF) x y)

end Stage

end PrimeCarleson.Proof.Fplus31
