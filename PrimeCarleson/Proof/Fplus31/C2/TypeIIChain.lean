module

public import PrimeCarleson.Proof.Fplus31.C2.TypeIIBoxes
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIEngine
public import PrimeCarleson.Proof.Fplus31.C2.TypeIIB5

/-!
# The type II step: boxes, engine on the product and extrapolation, end to end

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). From a
`LengStart` `S` (the start step) at degree `deg ∈ {1, 2}` and the type II output of the Vaughan
decomposition (the four-fold bound of `φ = 1_P · star (S.T.eval)` over `(L/2, L] × (M/2, M]`), the
steps compose:

1. The first half of the type II step (`type_two_boxes`): a class `b` mod `q`, `≥ x L² / (32 q)`
   pairs `(ℓ, ℓ') ∈ (L/2, L]²`, and for each a box of length `≥ x M / (8 q)` on which
   `m ↦ T.eval (ℓ (b + q m)) · conj (T.eval (ℓ' (b + q m)))` has bias `≥ x / 16`;
2. The second half of the type II step (`exists_pair_symbol_factorization`, with
   `controlledSymbolFactorization_mono_scale` to pass to the common scale `A ≤ x M / (8 q)`): the
   symbol of the product orbit of `D × D`, with the coordinates of `(δ_{ℓq} X, δ_{ℓ'q} X)`, has a
   `ControlledSymbolFactorization` for the frequency `(η, -η)` at the scale `A` of complexity
   `(P + C₁) ^ C₁`;
3. The extrapolation step, type II, on the vendored library's types
   (`symbol_dilation_extrapolation_typeII_clone`): a factorization of the undilated `X` relative to
   the common kernel `K⁰` at the scale `A L / 2`.

`type_two_extrapolation` is the composite. Its output is an `ExtrapolatedSymbolFactorizationII`,
which the sub-step (`exists_pointwise_polynomial_symbol_splitting` with `K = K⁰`) consumes, and
whose clauses on `η` feed the descending stage of the iteration.

-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- **Boxes, engine on the product and extrapolation for the type II step.** The constants `C₁` (the
engine) and `C₂` (the extrapolation) depend only on `deg`. Hypotheses: `S` a `LengStart` of
complexity `p`, a progression `P = {n ∈ [lo, hi] : n ≡ r (q)}` with `q ≤ e^p`, `q ≤ M`, the type II
output of the Vaughan decomposition for `φ = 1_P · star (S.T.eval)` (the four-fold bound
`x N² ≤ fourFold φ (L/2, L] (M/2, M]`, `L M < 4 N`, `0 < x ≤ 1`), the bias requirement
`e^{-P} ≤ x / 16` for `P = productNiltestBudget (p + 2) + 1`, and a box scale `A ≤ x M / (8 q)` with
`A ≥ e^{(P + C₁)^{C₁}}` and `A, L ≥ e^{C₂ (p̃ + log (32 q / x))³}`, `p̃ = (P + C₁)^{C₁}`.
Conclusion: a factorization of the undilated symbol of `S.T` at the scale `A L / 2`, relative to the
common kernel `K⁰`, of complexity `C₂ (p̃ + log (32 q / x) + 1)⁴`. -/
theorem type_two_extrapolation (deg : ℕ) (hdeg1 : 1 ≤ deg) (hdeg2 : deg ≤ 2) :
    ∃ (C₁ : ℕ) (C₂ : ℝ), 2 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ} (S : LengStart deg Q f p)
        {q : ℕ}, 1 ≤ q → (q : ℝ) ≤ Real.exp p → ∀ (r lo hi : ℤ) {N L M : ℕ},
        1 ≤ M → q ≤ M → (L : ℝ) * M < 4 * N →
        ∀ {x : ℝ}, 0 < x → x ≤ 1 → Real.exp (-(productNiltestBudget (p + 2) + 1)) ≤ x / 16 →
        x * (N : ℝ) ^ 2 ≤ fourFold (fun n : ℕ => typeISequence S.T q r lo hi (n : ℤ))
          (dyadicBlock L) (dyadicBlock M) →
        ∀ {A : ℝ}, A ≤ x * M / (8 * q) →
        Real.exp ((productNiltestBudget (p + 2) + 1 + C₁) ^ C₁) ≤ A →
        Real.exp (C₂ * (((productNiltestBudget (p + 2) + 1 + C₁) ^ C₁) +
          Real.log (1 / (x / (32 * q)))) ^ 3) ≤ A →
        Real.exp (C₂ * (((productNiltestBudget (p + 2) + 1 + C₁) ^ C₁) +
          Real.log (1 / (x / (32 * q)))) ^ 3) ≤ L →
        ExtrapolatedSymbolFactorizationII S.D.filtration S.D.basis S.omega S.hF S.η
          (A * L / 2) (S.T.symbol S.D.basis S.omega S.hF)
          (C₂ * (((productNiltestBudget (p + 2) + 1 + C₁) ^ C₁) +
            Real.log (1 / (x / (32 * q))) + 1) ^ 4) := by
  obtain ⟨C₁, hC₁, hG⟩ := exists_pair_symbol_factorization deg hdeg1
  obtain ⟨C₂, hC₂, hB5⟩ := symbol_dilation_extrapolation_typeII_clone
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro Q f p S q hq hqp r lo hi N L M hM hqM hLM x hx0 hx1 hbias hF A hAx hA1 hA2 hL
  have hT : (S.T.normBound : ℝ) ≤ 1 := by exact_mod_cast S.norm_le
  obtain ⟨b, Γ, hsub, hcard, hbox⟩ := type_two_boxes S.T hT hq r lo hi hM hqM hLM hx0 hx1 hF
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA1
  have hp0 : 0 ≤ p := S.nonneg
  have hbud := productNiltestBudget_geometry (p := p + 2) (by linarith)
  have hPp : 2 * p ≤ productNiltestBudget (p + 2) + 1 := by
    linarith only [hbud, hp0, sq_nonneg p]
  have hC1R : (2 : ℝ) ≤ C₁ := by exact_mod_cast hC₁
  set P := productNiltestBudget (p + 2) + 1 with hP
  have hP1 : 1 ≤ P := by linarith only [hbud, hp0, sq_nonneg p, hP]
  have hpp' : P ≤ (P + C₁) ^ C₁ :=
    calc P ≤ P + C₁ := by linarith
      _ ≤ (P + C₁) ^ C₁ := le_self_pow₀ (by linarith) (by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hex : ∀ pr : ℕ × ℕ, ∃ Y : (pairModel S.D).filtration.RealPolynomialSymbolGroup
      (fun _ : Unit => 1), pr ∈ Γ → ((∀ k : Fin (Fintype.card (Σ _ : Fin 2, Fin S.dim)),
        ((pairAssoc S.D S.omega S.hF).baseChange ℝ).repr Y.coord k =
          ((singleAssoc S.D S.omega S.hF).baseChange ℝ).repr
            (S.D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1)
              (if ((Fintype.equivFin (Σ _ : Fin 2, Fin S.dim)).symm k).1 = 0
                then ((q * pr.1 : ℕ) : ℚ) else ((q * pr.2 : ℕ) : ℚ))
              (S.T.symbol S.D.basis S.omega S.hF)).coord
            ((Fintype.equivFin (Σ _ : Fin 2, Fin S.dim)).symm k).2) ∧
        (pairModel S.D).filtration.ControlledSymbolFactorization (pairModel S.D).basis
          (pairWeight S.omega) (pairLayers S.hF) (pairFreq S.η) (fun _ : Unit => A) Y
          ((P + C₁) ^ C₁)) := by
    intro pr
    by_cases hpr : pr ∈ Γ
    · obtain ⟨o, len, hlen, hmean⟩ := hbox pr hpr
      have hlenA : A ≤ len := hAx.trans hlen
      have hlen0 : 0 < len := by
        have : (0 : ℝ) < len := lt_of_lt_of_le hApos hlenA
        exact_mod_cast this
      obtain ⟨Y, hY, hfac⟩ := hG S ((pr.1 : ℤ) * (q : ℤ)) ((pr.2 : ℤ) * (q : ℤ))
        ((pr.1 : ℤ) * b) ((pr.2 : ℤ) * b) o len hlen0 (C' := C₁) le_rfl (hA1.trans hlenA)
        (hbias.trans hmean)
      refine ⟨Y, fun _ => ⟨fun k => ?_, ?_⟩⟩
      · rw [hY k]
        have e0 : (((pr.1 : ℤ) * (q : ℤ) : ℤ) : ℚ) = ((q * pr.1 : ℕ) : ℚ) := by
          push_cast; ring
        have e1 : (((pr.2 : ℤ) * (q : ℤ) : ℤ) : ℚ) = ((q * pr.2 : ℕ) : ℚ) := by
          push_cast; ring
        rw [e0, e1]
      · exact controlledSymbolFactorization_mono_scale (pairModel S.D).filtration
          (pairModel S.D).basis (pairWeight S.omega) (pairLayers S.hF) hfac
          (fun _ => by exact_mod_cast hlen0) (fun _ => hApos) (fun _ => hlenA)
    · exact ⟨1, fun h => absurd h hpr⟩
  choose Y hY using hex
  have hc0 : 0 < x / (32 * q) := by positivity
  have hc1 : x / (32 * q) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith only [hx1, hq1]
  have hΓ : ∀ pr ∈ Γ, (L : ℝ) / 2 < pr.1 ∧ (pr.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < pr.2 ∧
      (pr.2 : ℝ) ≤ L := by
    intro pr hpr
    have h := Finset.mem_product.mp (hsub hpr)
    exact ⟨(mem_dyadicBlock.mp h.1).1, (mem_dyadicBlock.mp h.1).2, (mem_dyadicBlock.mp h.2).1,
      (mem_dyadicBlock.mp h.2).2⟩
  have hcard' : x / (32 * q) * (L : ℝ) ^ 2 ≤ Γ.card := by
    have : x / (32 * q) * (L : ℝ) ^ 2 = x / 32 * (L : ℝ) ^ 2 / q := by field_simp
    rw [this]
    exact hcard
  have hpP : p ≤ P := by linarith
  have h2d : (2 * S.dim : ℝ) ≤ (P + C₁) ^ C₁ := by
    have := S.complexity.1.1
    linarith
  exact hB5 hdeg1 hdeg2 S.D S.omega S.hF S.η ((P + C₁) ^ C₁) h2d
    (fun i j k => (S.complexity.1.2.2.1 i j k).trans (hpP.trans hpp')) (x / (32 * q)) hc0 hc1 q hq
    (hqp.trans (Real.exp_le_exp.mpr (hpP.trans hpp'))) L hL Γ hΓ hcard' A hA2
    (S.T.symbol S.D.basis S.omega S.hF) Y (fun pr hpr => (hY pr hpr).1)
    (fun pr hpr => (hY pr hpr).2)

end PrimeCarleson.Proof.Fplus31
