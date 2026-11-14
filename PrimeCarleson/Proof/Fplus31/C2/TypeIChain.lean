module

public import PrimeCarleson.Proof.Fplus31.C2.TypeI
public import PrimeCarleson.Proof.Fplus31.C2.Symbol

/-!
# The type I step: boxes, engine and extrapolation, end to end

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). From a
`LengStart` `S` (the start step) at degree `deg ∈ {1, 2}` and the type I output of the Vaughan
decomposition, the three steps compose:

1. The type I step (`type_one_boxes`): a class `b` mod `q`, `≥ δ L / q` integers `ℓ ∈ (L/2, L]`, and
   for each a box of length `≥ δ N / (q L)` on which `m ↦ S.T.eval (ℓ (b + q m))` has bias
   `≥ δ / 3`;
2. The engine of `G1/Compose.lean` (`exists_dilated_stride_symbol_factorization`, with
   `controlledSymbolFactorization_mono_scale` to pass to the common scale `A ≤ δ N / (q L)`): each
   `δ_{ℓ q} X`, `X = S.T.symbol`, has a `ControlledSymbolFactorization` at scale `A` of complexity
   `(p + C₁) ^ C₁`;
3. The extrapolation step on the library's types (`symbol_dilation_extrapolation_clone`): a
   factorization of the undilated `X` relative to `K = W + [gr, gr]` at the scale `A L / 2`.

`type_one_extrapolation` is the composite. Its output is an `ExtrapolatedSymbolFactorization`, which
the sub-step (`exists_pointwise_polynomial_symbol_splitting` with `K`) consumes.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- **Boxes, engine and extrapolation for the type I step.** The constants `C₁` (the engine) and
`C₂` (the extrapolation) depend only on `deg`. Hypotheses: `S` a `LengStart` of complexity `p`, a
progression `P = {n ∈ [lo, hi] : n ≡ r (q)}` with `q ≤ e^p`, `q L ≤ N`, the type I output of the
Vaughan decomposition for `φ = 1_P · star (S.T.eval)` (`δ L ≤ |Λ|`, the sums of norm `≥ δ N / L`),
the bias requirement `e^{-p} ≤ δ / 3` and a box scale `A ≤ δ N / (q L)` with `A ≥ e^{(p + C₁)^{C₁}}`
and `A ≥ e^{C₂ (p̃ + log (q / δ))³}`, `p̃ = (p + C₁)^{C₁}`. Conclusion: a factorization of the
undilated symbol of `S.T` at the scale `A L / 2`, relative to `K = W + [gr, gr]`, of complexity
`C₂ (p̃ + log (q / δ) + 1)⁴`. -/
theorem type_one_extrapolation (deg : ℕ) (hdeg1 : 1 ≤ deg) (hdeg2 : deg ≤ 2) :
    ∃ (C₁ : ℕ) (C₂ : ℝ), 2 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ} (S : LengStart deg Q f p)
        {q : ℕ}, 1 ≤ q → (q : ℝ) ≤ Real.exp p → ∀ (r lo hi : ℤ) {N N' L : ℕ},
        1 ≤ N → N' ≤ N → 1 ≤ L → q * L ≤ N →
        ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → Real.exp (-p) ≤ δ / 3 →
        ∀ {Λ : Finset ℕ}, (∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) → δ * L ≤ Λ.card →
        (∀ ℓ ∈ Λ, δ * ((N : ℝ) / L) ≤ ‖∑ n ∈ Finset.Icc 1 ⌊(N' : ℝ) / ℓ⌋₊,
          typeISequence S.T q r lo hi ((ℓ : ℤ) * n)‖) →
        ∀ {A : ℝ}, A ≤ δ * ((N : ℝ) / (q * L)) →
        Real.exp ((p + C₁) ^ C₁) ≤ A →
        Real.exp (C₂ * (((p + C₁) ^ C₁) + Real.log (1 / (δ / q))) ^ 3) ≤ A →
        ExtrapolatedSymbolFactorization S.D.filtration S.D.basis S.omega S.hF S.η
          (A * L / 2) (S.T.symbol S.D.basis S.omega S.hF)
          (C₂ * (((p + C₁) ^ C₁) + Real.log (1 / (δ / q)) + 1) ^ 4) := by
  obtain ⟨C₁, hC₁, hG⟩ := exists_dilated_stride_symbol_factorization deg hdeg1
  obtain ⟨C₂, hC₂, hB5⟩ := symbol_dilation_extrapolation_clone
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro Q f p S q hq hqp r lo hi N N' L hN hN' hL hqL δ hδ hδ1 hδp Λ hΛ hcard hsum A hAδ hA1 hA2
  have hT : (S.T.normBound : ℝ) ≤ 1 := by exact_mod_cast S.norm_le
  obtain ⟨b, Λ', hsub, hcard', hbox⟩ :=
    type_one_boxes S.T hT hq r lo hi hN hN' hL hqL hδ hΛ hcard hsum
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA1
  have hp0 : 0 ≤ p := S.nonneg
  have hC1R : (2 : ℝ) ≤ C₁ := by exact_mod_cast hC₁
  have hpp' : p ≤ (p + C₁) ^ C₁ := by
    calc p ≤ p + C₁ := by linarith
      _ ≤ (p + C₁) ^ C₁ := le_self_pow₀ (by linarith) (by omega)
  have hfac : ∀ ℓ ∈ Λ', S.D.filtration.ControlledSymbolFactorization S.D.basis S.omega S.hF S.η
      (fun _ : Unit => A) (S.D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1)
        (((q * ℓ : ℕ) : ℚ)) (S.T.symbol S.D.basis S.omega S.hF)) ((p + C₁) ^ C₁) := by
    intro ℓ hℓ
    obtain ⟨o, len, hlen, hmean⟩ := hbox ℓ hℓ
    have hlenA : A ≤ len := hAδ.trans hlen
    have hlen0 : 0 < len := by
      have : (0 : ℝ) < len := lt_of_lt_of_le hApos hlenA
      exact_mod_cast this
    have h1 := hG S (ℓ : ℤ) (q : ℤ) b o len hlen0 (C' := C₁) le_rfl (hA1.trans hlenA)
      (hδp.trans hmean)
    have h2 := controlledSymbolFactorization_mono_scale S.D.filtration S.D.basis S.omega S.hF h1
      (fun _ => by exact_mod_cast hlen0) (fun _ => hApos) (fun _ => hlenA)
    have e : ((((ℓ : ℤ) * (q : ℤ) : ℤ)) : ℚ) = ((q * ℓ : ℕ) : ℚ) := by push_cast; ring
    rw [e] at h2
    exact h2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine hB5 hdeg1 hdeg2 S.D.filtration S.D.basis S.omega S.hF S.η ((p + C₁) ^ C₁) ?_ ?_
    (δ / q) (by positivity) ?_ q hq ?_ L hL Λ' ?_ ?_ A hA2 (S.T.symbol S.D.basis S.omega S.hF) hfac
  · rw [Fintype.card_fin]
    exact S.complexity.1.1.trans hpp'
  · intro i j k
    exact (S.complexity.1.2.2.1 i j k).trans hpp'
  · rw [div_le_one hq0]
    linarith
  · exact hqp.trans (Real.exp_le_exp.mpr hpp')
  · intro ℓ hℓ
    exact hΛ ℓ (hsub hℓ)
  · rw [div_mul_eq_mul_div]
    exact hcard'

end PrimeCarleson.Proof.Fplus31
