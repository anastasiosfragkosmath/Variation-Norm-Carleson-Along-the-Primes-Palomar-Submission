module

public import PrimeCarleson.Proof.Fplus31.C2.Symbol
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIAlg

/-!
# The extrapolation step, type II variant, on the library's types: the output type

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The type
I output of `C2/Symbol.lean` is `ExtrapolatedSymbolFactorization`: a factorization of the undilated
symbol relative to `K = W + [gr, gr]` with `W` exposed (`η` kills the top layer of `W`). In the type
II step the subalgebra `W` lives in the product `gr × gr` and the output of the abstract
extrapolation (`Extrapolation/MainII.lean`) is a datum for the common kernel `K⁰ = (W + D × D)⁰`,
with the exposure `([k, k'], 0), (0, [k, k']) ∈ W₂` for `k, k' ∈ K⁰₁`. This file defines the
corresponding output `ExtrapolatedSymbolFactorizationII`, whose clauses on `η` are what the
descending stage of the iteration needs:

* `gradedFrequency_phi_symm`: the graded frequency `gradedFrequency η` of a vector in the
  coordinates `(g₁, g₂)` of the dictionary is `∑ x₁ i η (b i) + ∑ x₂ k η (b k)`;
* `ExtrapolatedSymbolFactorizationII`: `X = E P R` with `E` slow, `R` rational and `P ∈ exp (K_ℝ)`,
  `K ⊇ [gr, gr]` basis-graded and spanned by vectors of small height, `η [K, K] = 0` (the flag), and
  `η` kills the top layer of `K` as soon as it kills `[gr, gr]`;
* `extrapolatedSymbolFactorizationII_of_datum`: the translation from a datum of the abstract model.

-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section Freq

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

/-- **The graded frequency in the coordinates of `phi`.** -/
theorem gradedFrequency_phi_symm (hB : Step2Graded (F.associatedGradedBasis b ω hF) ω)
    (η : L →ₗ[ℚ] ℚ) (w : (Idx1 ω → ℚ) × (Idx2 ω → ℚ)) :
    F.gradedFrequency b ω hF η ((phi hB).symm w) =
      frLin (fun i : Idx1 ω => η (b i.1)) w.1 + frLin (fun k : Idx2 ω => η (b k.1)) w.2 := by
  have hphi : phi hB ((phi hB).symm w) = w := LinearEquiv.apply_symm_apply _ _
  have hc1 : ∀ i : Idx1 ω,
      (F.associatedGradedBasis b ω hF).repr ((phi hB).symm w) i.1 = w.1 i := fun i =>
    congrFun (congrArg Prod.fst hphi) i
  have hc2 : ∀ k : Idx2 ω,
      (F.associatedGradedBasis b ω hF).repr ((phi hB).symm w) k.1 = w.2 k := fun k =>
    congrFun (congrArg Prod.snd hphi) k
  change η (b.repr.symm ((F.associatedGradedBasis b ω hF).repr ((phi hB).symm w))) = _
  generalize (F.associatedGradedBasis b ω hF).repr ((phi hB).symm w) = c at hc1 hc2
  have hsum : b.repr.symm c = ∑ i, c i • b i := by
    conv_lhs => rw [← Basis.sum_repr b (b.repr.symm c)]
    simp
  rw [hsum, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← (splitIndexEquiv hB).sum_comp, Fintype.sum_sum_type]
  simp only [frLin_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (· * η (b i.1)) (hc1 i)
  · refine Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (· * η (b k.1)) (hc2 k)

end Freq

section Clone

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

/-- **A factorization of the undilated symbol relative to the common kernel `K = K⁰` of the type II
step**: `X = E P R` with `E` slow at scale `T`, `R` rational of denominator `m`, and `P ∈ exp (K_ℝ)`
where `K` is a basis-graded Lie subalgebra spanned by vectors of height `≤ p` containing `[gr, gr]`,
such that `η` kills the brackets `[K, K]` (the flag of the iteration) and, when `η` kills
`[gr, gr]`, the top layer of `K` (the top layer of the new model is killed and the iteration
descends). Compare `ExtrapolatedSymbolFactorization`, where `K = W + [gr, gr]` with `W` exposed; in
type II there is no `W` (it lives in the product). -/
def ExtrapolatedSymbolFactorizationII (η : L →ₗ[ℚ] ℚ) (T : ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)) (p : ℝ) : Prop :=
  ∃ (m : ℕ) (E P R : F.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (K : LieSubalgebra ℚ F.AssociatedGraded) (v : ι → F.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ E * P * R = X ∧
    F.SymbolSlowBound b ω hF (fun _ => 1) (fun _ : Unit => T) (Real.exp p) E ∧
    F.SymbolRationalGrid b ω hF (fun _ => 1) m R ∧
    Submodule.span ℚ (Set.range v) = K.toSubmodule ∧
    BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω K.toSubmodule ∧
    (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v i) j) ≤ p) ∧
    commutatorSubmodule F.AssociatedGraded ≤ K.toSubmodule ∧
    (∀ x ∈ K, ∀ y ∈ K, F.gradedFrequency b ω hF η ⁅x, y⁆ = 0) ∧
    ((∀ z ∈ commutatorSubmodule F.AssociatedGraded, F.gradedFrequency b ω hF η z = 0) →
      ∀ x ∈ K, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
        F.gradedFrequency b ω hF η x = 0) ∧
    P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) K)

/-- A datum for a graded subalgebra `K ⊇ D` of the abstract model, with `η` killing the brackets
of `K₁` and the top layer of `K` (the latter when `η` kills `D`), gives an
`ExtrapolatedSymbolFactorizationII`. -/
theorem extrapolatedSymbolFactorizationII_of_datum (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ)
    (K : GradedSubalg (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω))
    (hD : derived (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω) ≤ K.layer₂)
    (hflag : ∀ k ∈ K.layer₁, ∀ k' ∈ K.layer₁,
      frLin (fun k : Idx2 ω => η (b k.1))
        ((stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω).br k k') = 0)
    (htop₂ : s = 2 → (∀ x y, frLin (fun k : Idx2 ω => η (b k.1))
        ((stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω).br x y) = 0) →
      ∀ z ∈ K.layer₂, frLin (fun k : Idx2 ω => η (b k.1)) z = 0)
    (htop₁ : s = 1 → ∀ z ∈ K.layer₁, frLin (fun i : Idx1 ω => η (b i.1)) z = 0)
    {T p p' M : ℝ} (hp : p ≤ p') (hT : 0 < T) (hM : M ≤ Real.exp p') {m : ℕ}
    (hm : (m : ℝ) ≤ Real.exp p') {X : F.RealPolynomialSymbolGroup (fun _ : Unit => 1)}
    (h : Datum p K T M m ((symbolGroupEquiv F b ω hF hs1 hs2).symm X)) :
    ExtrapolatedSymbolFactorizationII F b ω hF η T X p' := by
  have hB := step2Graded_associatedGraded F b ω hF hs2
  obtain ⟨hgen, hm0, E, P, R, hprod, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨v, hv, hh⟩ := (gen_iff hB K (ofGraded hB K).toSubmodule
    (toSubmodule_eq_comap_ofGraded hB K) p).mp hgen
  have hMT : M / T ≤ Real.exp p' / T := div_le_div_of_nonneg_right hM hT.le
  have hMT2 : M / T ^ 2 ≤ Real.exp p' / T ^ 2 :=
    div_le_div_of_nonneg_right hM (by positivity)
  have hKgraded := basisGraded_ofGraded hB K
  have kE1 : ∀ (Z : SymbolGroup (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω))
      (i : Idx1 ω), ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (symbolGroupEquiv F b ω hF hs1 hs2 Z).coord i.1 = Z.fst i :=
    fun Z i => repr_realElt_fst _ ω Z i
  have kE2 : ∀ (Z : SymbolGroup (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω))
      (k : Idx2 ω), ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (symbolGroupEquiv F b ω hF hs1 hs2 Z).coord k.1 = Z.snd k :=
    fun Z k => repr_realElt_snd _ ω Z k
  -- the flag `η [K, K] = 0`
  have hbr : ∀ x y : F.AssociatedGraded, F.gradedFrequency b ω hF η ⁅x, y⁆ =
      frLin (fun k : Idx2 ω => η (b k.1))
        ((stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω).br (phi hB x).1 (phi hB y).1) := by
    intro x y
    have hx : ⁅x, y⁆ = (phi hB).symm (0, (stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω).br
        (phi hB x).1 (phi hB y).1) := by
      apply (phi hB).injective
      rw [phi_lie, LinearEquiv.apply_symm_apply]
    rw [hx, gradedFrequency_phi_symm F b ω hF hB η]
    simp
  have hfl : ∀ x ∈ ofGraded hB K, ∀ y ∈ ofGraded hB K, F.gradedFrequency b ω hF η ⁅x, y⁆ = 0 := by
    intro x hx y hy
    rw [hbr]
    exact hflag _ (K.fst_mem _ hx) _ (K.fst_mem _ hy)
  refine ⟨m, symbolGroupEquiv F b ω hF hs1 hs2 E, symbolGroupEquiv F b ω hF hs1 hs2 P,
    symbolGroupEquiv F b ω hF hs1 hs2 R, ofGraded hB K, v, hm0, hm, ?_, ?_, ?_, hv, hKgraded,
    fun i j => (hh i j).trans hp, ?_, hfl, ?_, ?_⟩
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
  · -- `[gr, gr] ⊆ K`
    intro z hz
    have hz' := commutator_le_comap hB hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_prod.mp (Submodule.mem_comap.mp hz')
    have hz0 : phi hB z = (0, (phi hB z).2) := Prod.ext (by simpa using hz1) rfl
    change phi hB z ∈ K.toSubmodule
    rw [hz0]
    exact GradedSubalg.mem_layer₂.mp (hD hz2)
  · -- the top layer
    intro hcomm x hx hxs
    have hDf : ∀ x y : Idx1 ω → ℚ, frLin (fun k : Idx2 ω => η (b k.1))
        ((stepTwoAlgebra (F.associatedGradedBasis b ω hF) ω).br x y) = 0 := by
      intro x y
      have h0 := hcomm _ (symm_zero_mem_commutator hB (br_mem_derived x y))
      rw [gradedFrequency_phi_symm F b ω hF hB η] at h0
      simpa using h0
    have hxK : phi hB x ∈ K.toSubmodule := hx
    have hxx : x = (phi hB).symm (phi hB x) := ((phi hB).symm_apply_apply x).symm
    rcases (by omega : s = 1 ∨ s = 2) with hs | hs
    · subst hs
      have hphx : phi hB x = ((phi hB x).1, 0) := by
        have := phi_gradeProjection_one hB x
        rw [hxs] at this
        refine Prod.ext rfl ?_
        exact congrArg Prod.snd this
      have hmem : (phi hB x).1 ∈ K.layer₁ := by
        rw [GradedSubalg.mem_layer₁, ← hphx]
        exact hxK
      rw [hxx, gradedFrequency_phi_symm F b ω hF hB η, htop₁ rfl _ hmem, hphx]
      simp
    · subst hs
      have hphx : phi hB x = (0, (phi hB x).2) := by
        have := phi_gradeProjection_two hB x
        rw [hxs] at this
        refine Prod.ext ?_ rfl
        exact congrArg Prod.fst this
      have hmem : (phi hB x).2 ∈ K.layer₂ := by
        rw [GradedSubalg.mem_layer₂, ← hphx]
        exact hxK
      rw [hxx, gradedFrequency_phi_symm F b ω hF hB η, htop₂ rfl hDf _ hmem]
      rw [hphx]
      simp
  · rw [symbolPointwiseSubalgebra_unit F b ω hF _ hKgraded]
    change (symbolGroupEquiv F b ω hF hs1 hs2 P).coord ∈
      (ofGraded hB K).toSubmodule.baseChange ℝ
    rw [mem_baseChange_iff hB, ← toSubmodule_eq_comap_ofGraded hB]
    change ((symbolOf _ ω (realElt _ ω P)).fst, (symbolOf _ ω (realElt _ ω P)).snd) ∈ _
    rw [symbolOf_realElt]
    exact h5

end Clone

end PrimeCarleson.Proof.Fplus31
