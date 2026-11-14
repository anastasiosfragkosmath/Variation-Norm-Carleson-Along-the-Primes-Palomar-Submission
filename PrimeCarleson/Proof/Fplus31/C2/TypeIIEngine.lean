module

public import PrimeCarleson.Proof.Fplus31.G1.Compose
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIPair
public import OAI.Combinatorics.Progressions.Nilpotent.CommonProductNiltestFamily
public import OAI.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency

/-!
# The type II step, second half: the engine on the pair model `D × D`

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The input
is a `LengStart` `S` (the start step, `G1/Start.lean`) and two stride-`q` dilated pullbacks `T₀`,
`T₁` of its niltest (`S.T.affinePullback` with `(a₀, c₀)`, `(a₁, c₁)`) whose product `T₀ · conj T₁`
has a bias on a box. The vendored library's `exists_common_product_niltest_family`
(`Nilpotent/CommonProductNiltestFamily.lean`) is applied to the one-element family on `D × D`
(`pi (fun _ : Fin 2 => D)`) with the base `![T₀, T₁]`, the observable of the second factor
conjugated (`Niltest.conjugate`, `conjugate_vertical`) and the frequency `(η, -η)`
(`C2/TypeIIPair.lean`, `pairFreq`). The resulting niltest on `D × D` has
`eval = T₀.eval · conj T₁.eval` and is vertical for `(η, -η)`, so the engine
`exists_translated_step_drop` (on the filtration of `D × D` with the product basis and the weights
`pairWeight`) applies, as in `G1/Compose.lean` for one factor. The statement does not mention the
product niltest: it produces the symbol `Y` of the product orbit, with the coordinates of
`(δ_{a₀} X, δ_{a₁} X)` (`pair_orbitSymbol_repr`, `affinePullback_unit_symbol`), and its
`ControlledSymbolFactorization`.

* `rationalLogHeight_neg'`: the height is invariant under negation;
* `exists_pair_symbol_factorization`: the closed statement.

-/

@[expose] public noncomputable section

open OAI OAI.Erdos3 OAI.Erdos3.CircleFourier
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The height of a rational number is invariant under negation. -/
theorem rationalLogHeight_neg' (q : ℚ) : rationalLogHeight (-q) = rationalLogHeight q := by
  simp [rationalLogHeight]

open RationalFilteredNilmanifold

/-- **The engine on the pair model `D × D`.**  Let `S` be a `LengStart` of degree `deg ≥ 1` and
`T₀`, `T₁` two stride-`q` dilated pullbacks of its niltest.  If the product `T₀ · conj T₁` has bias
`≥ e^{-P}` on a box of length `len ≥ e^{(P + C')^{C'}}` (`P = productNiltestBudget (p + 2) + 1`,
`C' ≥ C`), then the symbol `Y` of the product orbit of `D × D` has a `ControlledSymbolFactorization`
for the frequency `(η, -η)` at the box scale `len`, of complexity `(P + C)^C`; and the coordinates
of `Y` are those of the two dilated symbols of `T`. -/
theorem exists_pair_symbol_factorization (deg : ℕ) (hdeg : 1 ≤ deg) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
      (S : LengStart deg Q f p) (a₀ a₁ c₀ c₁ o : ℤ) (len : ℕ), 0 < len →
      ∀ {C' : ℕ}, C ≤ C' → Real.exp ((productNiltestBudget (p + 2) + 1 + C') ^ C') ≤ len →
      Real.exp (-(productNiltestBudget (p + 2) + 1)) ≤
        ‖𝔼 m ∈ translatedIntegerBox (fun _ : Unit => o) (fun _ : Unit => len),
          (S.T.affinePullback (fun (_ : Unit) (_ : Unit) => a₀) (fun _ : Unit => c₀)).eval m *
            star ((S.T.affinePullback (fun (_ : Unit) (_ : Unit) => a₁)
              (fun _ : Unit => c₁)).eval m)‖ →
      ∃ Y : (pairModel S.D).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1),
        (∀ k : Fin (Fintype.card (Σ _ : Fin 2, Fin S.dim)),
          ((pairAssoc S.D S.omega S.hF).baseChange ℝ).repr Y.coord k =
            ((singleAssoc S.D S.omega S.hF).baseChange ℝ).repr
              (S.D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1)
                (if ((Fintype.equivFin (Σ _ : Fin 2, Fin S.dim)).symm k).1 = 0
                  then (a₀ : ℚ) else (a₁ : ℚ))
                (S.T.symbol S.D.basis S.omega S.hF)).coord
              ((Fintype.equivFin (Σ _ : Fin 2, Fin S.dim)).symm k).2) ∧
        (pairModel S.D).filtration.ControlledSymbolFactorization (pairModel S.D).basis
          (pairWeight S.omega) (pairLayers S.hF) (pairFreq S.η) (fun _ : Unit => (len : ℝ)) Y
          ((productNiltestBudget (p + 2) + 1 + C) ^ C) := by
  obtain ⟨C₀, hC₀, hspec⟩ := exists_translated_step_drop.{0, 0} deg hdeg
  refine ⟨C₀ + 1, by omega, ?_⟩
  intro Q f p S a₀ a₁ c₀ c₁ o len hlen C' hC' hlarge hbias
  obtain ⟨τ, hA, hM, hT2⟩ := exists_real_module_topology
    (RationalFilteredNilmanifold.productFinBasis (fun _ : Fin 2 => S.D))
  let := τ
  let := hA
  let := hM
  let := hT2
  have hp : 0 ≤ p := S.nonneg
  have hbud := productNiltestBudget_geometry (p := p + 2) (by linarith)
  have hP4 : 16 ≤ productNiltestBudget (p + 2) := by nlinarith
  have hPp : p + 2 ≤ productNiltestBudget (p + 2) := by nlinarith
  have hPmono : productNiltestBudget (p + 2) ≤ productNiltestBudget (p + 2) + 1 := by linarith
  let T₀ := S.T.affinePullback (fun (_ : Unit) (_ : Unit) => a₀) (fun _ : Unit => c₀)
  let T₁ := S.T.affinePullback (fun (_ : Unit) (_ : Unit) => a₁) (fun _ : Unit => c₁)
  let base : Fin 2 → S.D.Niltest (fun _ : Unit => 1) := fun i => if i = 0 then T₀ else T₁
  let Tf : Unit → Fin 2 → S.D.Niltest (fun _ : Unit => 1) :=
    fun _ i => if i = 0 then T₀ else T₁.conjugate
  let eta : Unit → Fin 2 → S.L →ₗ[ℚ] ℚ := fun _ i => if i = 0 then S.η else -S.η
  have hc0 : T₀.ComplexityLE (p + 2) := S.complexity.mono (by linarith)
  have hc1 : T₁.ComplexityLE (p + 2) := S.complexity.mono (by linarith)
  obtain ⟨S0, Sf, hS0orb, hS0c, hSf⟩ := exists_common_product_niltest_family
    (fun _ : Fin 2 => S.D) base Tf (fun _ => Finset.univ) eta (p := p + 2) (by linarith)
    (by simp; linarith) (fun _ => S.complexity.1.mono S.D (by linarith))
    (fun j i _ => by
      by_cases hi : i = 0
      · simp [Tf, base, hi]
      · simp only [Tf, base, hi, ite_false]
        rfl)
    (fun j i _ => by
      by_cases hi : i = 0
      · simp only [Tf, hi, ite_true]
        exact hc0
      · simp only [Tf, hi, ite_false]
        exact hc1)
    (fun j i _ => by
      by_cases hi : i = 0
      · simp only [Tf, hi, ite_true]
        exact S.norm_le
      · simp only [Tf, hi, ite_false]
        exact S.norm_le)
    (fun j i _ k => by
      by_cases hi : i = 0
      · simp only [eta, hi, ite_true]
        exact (S.eta_height k).trans (by linarith)
      · simp only [eta, hi, ite_false, LinearMap.neg_apply, rationalLogHeight_neg']
        exact (S.eta_height k).trans (by linarith))
    (fun j i _ z hz x => by
      by_cases hi : i = 0
      · simp only [Tf, eta, hi, ite_true]
        exact S.vertical z hz x
      · simp only [Tf, eta, hi, ite_false]
        exact Niltest.conjugate_vertical T₁ S.η (fun z hz x => S.vertical z hz x) z hz x)
  obtain ⟨horb, -, hcp, hev, hht, hvt⟩ := hSf ()
  have hsel : selectedOrbitFrequencies (eta ()) Finset.univ = eta () := funext fun i => by
    simp [selectedOrbitFrequencies]
  rw [hsel] at hht hvt
  have heval : ∀ x, (Sf ()).eval x = T₀.eval x * star (T₁.eval x) := fun x => by
    rw [hev x, Fin.prod_univ_two]
    simp [Tf]
  have hlarge' : ∀ _ : Unit,
      Real.exp ((productNiltestBudget (p + 2) + 1 + C₀) ^ C₀) ≤ (len : ℝ) := by
    intro _
    refine le_trans (Real.exp_le_exp.mpr ?_) hlarge
    have hC'1 : (1 : ℝ) ≤ productNiltestBudget (p + 2) + 1 + C' := by
      have : (0 : ℝ) ≤ C' := Nat.cast_nonneg _
      linarith
    have hC0 : (C₀ : ℝ) ≤ C' := by exact_mod_cast (by omega : C₀ ≤ C')
    calc (productNiltestBudget (p + 2) + 1 + C₀) ^ C₀
        ≤ (productNiltestBudget (p + 2) + 1 + C') ^ C₀ := by
          apply pow_le_pow_left₀ (by positivity)
          linarith
      _ ≤ (productNiltestBudget (p + 2) + 1 + C') ^ C' :=
          pow_le_pow_right₀ hC'1 (by omega)
  have hbias' : Real.exp (-(productNiltestBudget (p + 2) + 1)) ≤
      ‖𝔼 m ∈ translatedIntegerBox (fun _ : Unit => o) (fun _ : Unit => len), (Sf ()).eval m‖ := by
    simpa only [heval] using hbias
  have hfac := hspec (pairModel S.D) (pairWeight S.omega) (pairLayers S.hF)
    (productNiltestBudget (p + 2) + 1) (by linarith) (by simp; linarith) (Sf ())
    (hcp.mono hPmono) (pairFreq S.η)
    (fun k => (hht k).trans (by linarith)) hvt (fun _ => o) (fun _ => len) (fun _ => hlen)
    hlarge' hbias'
  have hsymb : ∀ i : Fin 2, orbitSymbol S.D.filtration S.D.basis S.omega S.hF (base i).orbit =
      S.D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1)
        (if i = 0 then (a₀ : ℚ) else (a₁ : ℚ)) (S.T.symbol S.D.basis S.omega S.hF) := by
    intro i
    by_cases hi : i = 0
    · simp only [base, hi, ite_true]
      exact affinePullback_unit_symbol S.T S.D.basis S.omega S.hF a₀ c₀
    · simp only [base, hi, ite_false]
      exact affinePullback_unit_symbol S.T S.D.basis S.omega S.hF a₁ c₁
  have hsym : (Sf ()).symbol (pairModel S.D).basis (pairWeight S.omega) (pairLayers S.hF) =
      orbitSymbol (pairModel S.D).filtration (pairModel S.D).basis (pairWeight S.omega)
        (pairLayers S.hF) (NilpotentLieFiltration.piRealOrbit (fun _ : Fin 2 => S.D.filtration)
          (fun i => (base i).orbit)) := by
    change orbitSymbol _ _ _ _ (Sf ()).orbit = _
    rw [horb, hS0orb]
  rw [hsym] at hfac
  refine ⟨orbitSymbol (pairModel S.D).filtration (pairModel S.D).basis (pairWeight S.omega)
    (pairLayers S.hF) (NilpotentLieFiltration.piRealOrbit (fun _ : Fin 2 => S.D.filtration)
      (fun i => (base i).orbit)), fun k => ?_, ?_⟩
  · rw [pair_orbitSymbol_repr S.hF (fun i => (base i).orbit) k]
    simp only [hsymb]
  · refine NilpotentLieFiltration.ControlledSymbolFactorization.mono (pairModel S.D).filtration
      (pairModel S.D).basis (pairWeight S.omega) (pairLayers S.hF) hfac ?_
      (fun _ => by exact_mod_cast hlen)
    have hb1 : (1 : ℝ) ≤ productNiltestBudget (p + 2) + 1 + C₀ := by
      have : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
      linarith
    calc (productNiltestBudget (p + 2) + 1 + C₀) ^ C₀
        ≤ (productNiltestBudget (p + 2) + 1 + ((C₀ + 1 : ℕ) : ℝ)) ^ C₀ := by
          apply pow_le_pow_left₀ (by positivity)
          push_cast
          linarith
      _ ≤ (productNiltestBudget (p + 2) + 1 + ((C₀ + 1 : ℕ) : ℝ)) ^ (C₀ + 1) := by
          apply pow_le_pow_right₀ _ (by omega)
          push_cast
          linarith

end PrimeCarleson.Proof.Fplus31
