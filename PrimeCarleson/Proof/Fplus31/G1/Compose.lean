module

public import PrimeCarleson.Proof.Fplus31.G1.Dilation
public import PrimeCarleson.Proof.Fplus31.G1.Start
public import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree
public import OAI.Combinatorics.Progressions.Estimates.SquareGradedRelative
public import OAI.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
public import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
public import OAI.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial

/-!
# Composition of the start step, the dilation lemma and the single-niltest engine

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). From a
`LengStart` (the start step, `G1/Start.lean`) and one stride-`q` dilated pullback of its niltest
(Leng's Prop 5.2 step, arXiv:2312.10772v5 TeX L1130-L1138), the engine
`OAI.Erdos3.exists_translated_step_drop` produces a `ControlledSymbolFactorization` of the symbol of
the pullback, which is `δ_{ℓ q}` of the symbol of the start niltest (the dilation lemma,
`G1/Dilation.lean`):

* `controlledSymbolFactorization_mono_scale`: a controlled factorization at box scale `S` is one at
  every smaller scale `T ≤ S`, so the minimum of the box lengths of the dilates is a common scale
  (slow bounds are monotone in the scale);
* `symbolPointwiseSubalgebra_unit`: for the one-variable symbol (`σ = Unit`) and a basis-graded
  subalgebra `W` of `gr L`, the vendored library's `symbolPointwiseSubalgebra W` (the subalgebra the
  factor `P` of a `ControlledSymbolFactorization` lies in) is `W` itself, so `P ∈ exp (W_ℝ)` as in
  the datum of the extrapolation step;
* `exists_dilated_stride_symbol_factorization`: the closed statement. The only hypotheses are the
  ones of the engine: the box length `len` satisfies `exp ((p + C') ^ C') ≤ len` for some `C' ≥ C`
  (the engine constant `C`; a consumer that needs a larger lower bound on `len`, as the
  extrapolation step does, takes `C'` large), and the bias of the pullback on the box.

Used by the type I and type II steps (the engine entry) and by the extrapolation step (its input).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3 OAI.Erdos3.CircleFourier
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section PointwiseUnit

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

/-- The coefficient of the monomial `t ^ n` of the polynomial form of a one-variable symbol `x`
is its grade-`n` component. -/
theorem coefficients_gradedSymbolPolynomial_unit (x : F.AssociatedGraded) (n : ℕ) :
    VectorPolynomial.coefficients (F.gradedSymbolPolynomial b ω hF (fun _ : Unit => 1) x)
        (unitMonomial n) =
      basisGradeProjection (F.associatedGradedBasis b ω hF) ω n x := by
  apply (F.associatedGradedBasis b ω hF).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases h : ω i = n
  · subst h
    rw [ite_eq_left rfl, F.associatedGradedBasis_repr]
    exact F.gradedSymbolPolynomial_coefficient b ω hF (fun _ : Unit => 1) x
      ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩
  · rw [ite_eq_right h]
    exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hF (fun _ : Unit => 1) x _ i
      (by rw [weight_unitMonomial]; exact fun h' => h h'.symm)

/-- For a basis-graded subalgebra `U` of `gr L`, a one-variable symbol lies in
`symbolPointwiseSubalgebra U` exactly when it lies in `U`. -/
theorem mem_symbolPointwiseSubalgebra_unit_iff (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule)
    (x : F.AssociatedGraded) :
    x ∈ F.symbolPointwiseSubalgebra b ω hF (fun _ : Unit => 1) U ↔ x ∈ U := by
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  constructor
  · intro h
    let B := F.associatedGradedBasis b ω hF
    let J := (B.repr x).support.sup ω + 1
    have hx : basisBelowProjection B ω J x = x := by
      apply B.repr.injective
      ext i
      rw [basisBelowProjection_repr]
      by_cases hi : B.repr x i = 0
      · simp [hi]
      · have hlt : ω i < J :=
          Nat.lt_succ_of_le (Finset.le_sup (f := ω) (Finsupp.mem_support_iff.mpr hi))
        rw [ite_eq_left hlt]
    rw [← hx, basisBelowProjection_eq_sum_grades]
    refine Submodule.sum_mem U.toSubmodule fun k _ => ?_
    rw [← coefficients_gradedSymbolPolynomial_unit]
    exact h _
  · intro hx α
    rw [← unitMonomial_weight α, coefficients_gradedSymbolPolynomial_unit]
    exact hU _ x hx

/-- For the one-variable symbol the pointwise subalgebra of a basis-graded subalgebra `U` of
`gr L` is `U` itself. -/
theorem symbolPointwiseSubalgebra_unit (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule) :
    F.symbolPointwiseSubalgebra b ω hF (fun _ : Unit => 1) U = U :=
  LieSubalgebra.ext _ _ fun x => mem_symbolPointwiseSubalgebra_unit_iff F b ω hF U hU x

end PointwiseUnit

/-- **Scale monotonicity.** A controlled symbol factorization at the box scale `S` is a controlled
symbol factorization at every smaller scale `T ≤ S`: the minimum of the box lengths of several
dilates is a common scale. -/
theorem controlledSymbolFactorization_mono_scale {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) {η : L →ₗ[ℚ] ℚ}
    {S T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η S X p) (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    (hTS : ∀ i, T i ≤ S i) : F.ControlledSymbolFactorization b ω hF η T X p := by
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hh, hη, hP⟩ := h
  refine ⟨m, E, P, R, W, v, hm, hmp, hprod, ?_, hR, hv, hW, hh, hη, hP⟩
  have hresc := F.symbolSlowBound_rescale b ω hF S T hS hT (p := p) (q := 0) le_rfl
    (fun i => by simpa using hTS i) E hE
  simpa using hresc

/-- **Composition.** Let `S` be a `LengStart` of degree `deg ≥ 1` and complexity `p`, with adapted
basis `S.D.basis` of weights `S.omega` and vertical frequency `S.η`. If the stride-`q` dilated,
translated pullback `x ↦ ℓ (b + q x)` of `S.T` has bias at least `e^{-p}` on a box of length
`len ≥ exp ((p + C') ^ C')` (`C' ≥ C`), then the symbol `δ_{ℓ q} X`, `X = S.T.symbol`, has a
controlled factorization (`E P R` with `E` slow at scale `len`, `R` rational, `P` in the graded
subalgebra `W`, `η` killing the top layer of `W`) of complexity `(p + C) ^ C`. -/
theorem exists_dilated_stride_symbol_factorization (deg : ℕ) (hdeg : 1 ≤ deg) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (S : LengStart deg Q f p) (ℓ q b o : ℤ) (len : ℕ), 0 < len →
      ∀ {C' : ℕ}, C ≤ C' → Real.exp ((p + C') ^ C') ≤ len →
      Real.exp (-p) ≤ ‖𝔼 m ∈ translatedIntegerBox (fun _ : Unit => o) (fun _ : Unit => len),
        (S.T.affinePullback (fun _ _ => ℓ * q) (fun _ => ℓ * b)).eval m‖ →
      S.D.filtration.ControlledSymbolFactorization S.D.basis S.omega S.hF S.η
        (fun _ => (len : ℝ))
        (S.D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1) ((ℓ * q : ℤ) : ℚ)
          (S.T.symbol S.D.basis S.omega S.hF)) ((p + C) ^ C) := by
  obtain ⟨C₀, hC₀, hspec⟩ := exists_translated_step_drop.{0, 0} deg hdeg
  refine ⟨C₀ + 1, by omega, ?_⟩
  intro Q f p S ℓ q b o len hlen C' hC' hlarge hbias
  have hp : 0 ≤ p := S.nonneg
  have hσ : (Fintype.card Unit : ℝ) ≤ p + 1 := by simp; linarith
  have hC'1 : (1 : ℝ) ≤ p + C' := by
    have : (3 : ℝ) ≤ C' := by exact_mod_cast (show 3 ≤ C' by omega)
    linarith
  have hlarge' : ∀ _ : Unit, Real.exp ((p + 1 + C₀) ^ C₀) ≤ (len : ℝ) := by
    intro _
    refine le_trans (Real.exp_le_exp.mpr ?_) hlarge
    calc (p + 1 + C₀) ^ C₀ ≤ (p + C') ^ C₀ := by
          apply pow_le_pow_left₀ (by positivity)
          have : (C₀ + 1 : ℝ) ≤ C' := by exact_mod_cast hC'
          linarith
      _ ≤ (p + C') ^ C' := pow_le_pow_right₀ hC'1 (by omega)
  have hbias' : Real.exp (-(p + 1)) ≤
      ‖𝔼 m ∈ translatedIntegerBox (fun _ : Unit => o) (fun _ : Unit => len),
        (S.T.affinePullback (fun _ _ => ℓ * q) (fun _ => ℓ * b)).eval m‖ :=
    (Real.exp_le_exp.mpr (by linarith)).trans hbias
  have hfac := hspec S.D S.omega S.hF (p + 1) (by linarith) hσ
    (S.T.affinePullback (fun _ _ => ℓ * q) (fun _ => ℓ * b))
    (S.complexity.mono (by linarith)) S.η (fun i => (S.eta_height i).trans (by linarith))
    S.vertical (fun _ => o) (fun _ => len) (fun _ => hlen) hlarge' hbias'
  rw [affinePullback_stride_symbol] at hfac
  refine NilpotentLieFiltration.ControlledSymbolFactorization.mono S.D.filtration S.D.basis
    S.omega S.hF hfac ?_ (fun _ => by exact_mod_cast hlen)
  have hb1 : (1 : ℝ) ≤ p + ((C₀ + 1 : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ C₀ := by exact_mod_cast hC₀
    push_cast
    linarith
  calc (p + 1 + C₀) ^ C₀ = (p + ((C₀ + 1 : ℕ) : ℝ)) ^ C₀ := by push_cast; ring_nf
    _ ≤ (p + ((C₀ + 1 : ℕ) : ℝ)) ^ (C₀ + 1) := pow_le_pow_right₀ hb1 (by omega)

end PrimeCarleson.Proof.Fplus31
