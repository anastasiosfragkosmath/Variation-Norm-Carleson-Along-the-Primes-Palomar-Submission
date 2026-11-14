module

public import PrimeCarleson.Proof.Fplus31.C2.Lift
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIClone

/-!
# The sub-step, type II: the lift from the symbol factorization to the orbit-level factors

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1).
`Lift.lean` lifts an `ExtrapolatedSymbolFactorization` (type I, with `K = W + [gr, gr]` and `W`
exposed). In the type II step the subalgebra is the common kernel `K⁰` of the product and there is
no `W` (`C2/TypeIIClone.lean`); the lift is the same (the splitting
`exists_pointwise_polynomial_symbol_splitting` with the single subalgebra `U = K`, the lattice
normalization and the slow left constant), but the conclusion returns the properties of `K` that the
iteration needs, for `R.subalgebra`, in place of the exposed `W`:

* `exists_orbitFactors_of_extrapolatedII`: a `NativePolynomialOrbitFactors` with
  `subalgebra = K⁰`, basis-graded, containing `[gr, gr]`, `η [K, K] = 0` and
  `η` kills the top layer of `K` as soon as it kills `[gr, gr]`.

-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration VectorPolynomial

/-- **The lift for the type II output.** As `exists_orbitFactors_of_extrapolated`, but
from an `ExtrapolatedSymbolFactorizationII`: the `NativePolynomialOrbitFactors` has `subalgebra = K`
(the common kernel `K⁰`), and the properties of `K` that the iteration needs are returned for
`R.subalgebra`: basis-graded, containing `[gr, gr]`, `η` kills `[K, K]` (the flag), and `η` kills
the top layer of `K` when it kills `[gr, gr]`. -/
theorem exists_orbitFactors_of_extrapolatedII (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] (D : RationalFilteredNilmanifold L s d),
      d = finrank ℚ L → ∀ (ω : Fin d → ℕ)
        (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})) {p : ℝ},
      1 ≤ p → D.GeometryComplexityLE p →
      ∀ (η : L →ₗ[ℚ] ℚ)
        (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group)
        (A : ℝ), Real.exp ((p + C) ^ C) ≤ A →
      ExtrapolatedSymbolFactorizationII D.filtration D.basis ω hF η A
        (D.filtration.realPolynomialSymbolHom D.basis ω hF (fun _ : Unit => 1) g) p →
      ∃ R : NativePolynomialOrbitFactors D g (0 : L →ₗ[ℚ] ℚ) (fun _ : Unit => A) ((p + C) ^ C),
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω
          R.subalgebra.toSubmodule ∧
        commutatorSubmodule D.filtration.AssociatedGraded ≤ R.subalgebra.toSubmodule ∧
        (∀ x ∈ R.subalgebra, ∀ y ∈ R.subalgebra,
          D.filtration.gradedFrequency D.basis ω hF η ⁅x, y⁆ = 0) ∧
        ((∀ z ∈ commutatorSubmodule D.filtration.AssociatedGraded,
            D.filtration.gradedFrequency D.basis ω hF η z = 0) →
          ∀ x ∈ R.subalgebra, basisGradeProjection (D.filtration.associatedGradedBasis D.basis ω hF)
            ω s x = x → D.filtration.gradedFrequency D.basis ω hF η x = 0) := by
  obtain ⟨c, _, hnormalize⟩ := exists_native_polynomial_normalization.{0, 0} s
  obtain ⟨k, hk2, hsplit⟩ := exists_pointwise_polynomial_symbol_splitting.{0, 0, 0, 0, 0} s 1
  obtain ⟨l, _, hleft⟩ := exists_native_slow_left_constant_bound.{0, 0} s
  let N : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let F₁ : Polynomial ℕ := (Polynomial.X + 3) ^ k
  let Q : Polynomial ℕ := Polynomial.X + N + F₁
  let P : Polynomial ℕ := F₁ + (Q + Polynomial.C l) ^ l + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ D hd ω hF p hp1 hD η g A hA hX
  subst hd
  have hp0 : 0 ≤ p := by linarith
  let q := p + (p + c) ^ c + (p + 3) ^ k
  have hn0 : 0 ≤ (p + c) ^ c := by positivity
  have hf0 : 0 ≤ (p + 3) ^ k := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hnq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hfq : (p + 3) ^ k ≤ q := by dsimp [q]; linarith
  have hb : (p + 3) ^ k + (q + l) ^ l + p + 2 ≤ (p + C) ^ C := by
    simpa [P, Q, N, F₁, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hl0 : 0 ≤ (q + l) ^ l := by positivity
  have hfC : (p + 3) ^ k ≤ (p + C) ^ C := by linarith
  have hlC : (q + l) ^ l ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
  have hp3 : p + 1 + 2 = p + 3 := by ring
  obtain ⟨a₀, κ, g₀, ha₀, hκ, hnormEq, hg₀zero, hsymbol⟩ :=
    hnormalize D ω hF (fun _ : Unit => 1) p hp0 hD g
  obtain ⟨m, E, P', R, K, v, hm0, hmp, hprod, hE, hR, hv, hKg, hh, hcomm, hflag, htop, hP⟩ := hX
  have hAg : ∀ _i : Unit, Real.exp ((p + 1 + 2) ^ k) ≤ (fun _ : Unit => A) _i := by
    intro _
    refine le_trans (Real.exp_le_exp.mpr ?_) hA
    rw [hp3]
    exact hfC
  have hcardF : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1)
  have hcardU : (Fintype.card Unit : ℝ) ≤ p + 1 := by simp; linarith
  obtain ⟨m', e₀, p₀, r₀, hm', hm'p, hdvd, hfactor, hmid, he, hr, he0, hr0, hp0c⟩ :=
    hsplit D.filtration D.basis ω hF (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)
      (fun _ : Unit => K) (fun _ : Unit => v) (fun _ => hv) (fun _ => hKg)
      ⌈Real.exp p⌉₊ m (p + 1) (Nat.ceil_pos.mpr (Real.exp_pos p)) hm0 (by linarith)
      hcardF hcardU hcardF hcardU (ceil_exp_le_exp_add_one hp0)
      (hmp.trans (Real.exp_le_exp.mpr (by linarith)))
      (fun i j k' => rationalHeightLE_ceil_exp (hD.2.2.1 i j k'))
      (fun _ i k' => rationalHeightLE_ceil_exp (hh i k'))
      (fun _ : Unit => A) hAg g₀ (fun _ => E) (fun _ => P') (fun _ => R)
      (fun _ => hprod.trans hsymbol.symm)
      (fun _ => (D.filtration.mem_real_symbolPointwiseSubalgebra_iff_values D.basis ω hF
        (fun _ : Unit => 1) K P'.coord).mp hP)
      (fun _ => D.filtration.symbolSlowBound_mono D.basis ω hF (fun _ : Unit => 1)
        (fun _ : Unit => A) (fun _ => hApos)
        (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith)) E hE)
      (fun _ => hR)
  have hfq' : (p + 1 + 2) ^ k ≤ q := by rw [hp3]; exact hfq
  have hsmall := hleft D ω hF q hq (hD.mono D hpq) (by simp; linarith) (fun _ : Unit => A)
    (fun _ => hApos) a₀ (fun i => (ha₀ i).trans (Real.exp_le_exp.mpr hnq)) e₀
    (D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) (fun _ : Unit => A)
      (fun _ => hApos) (Real.exp_le_exp.mpr hfq') e₀ he)
  have hprodR : D.filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) a₀ * e₀ *
      p₀ * r₀ * D.filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) κ = g := by
    calc _ = D.filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) a₀ *
          (e₀ * p₀ * r₀) * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ := by
          simp only [mul_assoc]
      _ = g := by rw [hfactor]; exact hnormEq
  have hmid' : ∀ t : Unit → ℝ, eval₂ t (D.filtration.realGradedSymbolPolynomial D.basis ω hF
      (fun _ : Unit => 1) (D.filtration.realPolynomialSymbolHom D.basis ω hF (fun _ : Unit => 1)
        p₀).coord) ∈ realificationLieSubalgebra K := by
    simpa only [iInf_const] using hmid
  have hp''0 : 0 ≤ (p + C) ^ C := hp0.trans hpC
  exact ⟨{
    basis := D.basis
    weight := ω
    adapted := hF
    basis_height := fun i j => rationalLogHeight_repr_basis_le D.basis hp''0 i j
    subalgebra := K
    generator := v
    spanning := hv
    graded := hKg
    generator_height := fun i j => (hh i j).trans hpC
    kills_top := fun z _ => realifyFunctional_zero z
    denominator := m'
    denominator_pos := hm'
    denominator_bound := hm'p.trans (Real.exp_le_exp.mpr (hfC.trans' (by rw [hp3])))
    latticeConstant := κ
    latticeConstant_mem := hκ
    slow := D.filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) a₀ * e₀
    middle := p₀
    rational := r₀
    product := hprodR
    slow_bound := fun α i => (hsmall α i).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hlC)
        (monomialScale_pos (fun _ : Unit => A) (fun _ => hApos) α).le)
    rational_grid := hr
    middle_zero := hp0c.trans hg₀zero
    rational_zero := hr0
    middle_coefficients :=
      (D.filtration.real_symbol_values_iff_refiltration_coefficients D.basis ω hF
        (fun _ : Unit => 1) K p₀.coord).mp hmid' }, hKg, hcomm, hflag, htop⟩

end PrimeCarleson.Proof.Fplus31
