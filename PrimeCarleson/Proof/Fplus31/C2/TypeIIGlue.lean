module

public import PrimeCarleson.Proof.Fplus31.C2.TypeIIChain

/-!
# The Vaughan decomposition feeds the type II step: its type II output, end to end

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
Vaughan decomposition (`TypeIII/Main.lean`, `vonMangoldt_sub_cramer_typeI_or_typeII`) gives, for
`φ = typeISequence T q r lo hi = 1_P · star (T.eval)` and `Λ - Λ_{C,w}`, either the type I data
(consumed by `C2/TypeIChain.lean`) or the type II four-fold bound with `N < L³ ≤ N²`, `N < M³ ≤ N²`,
`L M < 4 N` and `η⁴ N² / (2²⁰ (1 + log N)¹⁸) ≤ fourFold φ (L/2, L] (M/2, M]`. Here that output is
fed to `type_two_extrapolation` (`C2/TypeIIChain.lean`) with `x = typeIIx η N`, the constant of the
four-fold bound capped at one as `typeII_pairs` requires; `1 ≤ M` and `q ≤ M` follow from the
hypothesis `q³ ≤ N` and `N < M³`.

-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The type II parameter `x = min (η⁴ / (2²⁰ (1 + log N)¹⁸)) 1` (the four-fold bound of the Vaughan
decomposition with the constant capped at one, as `typeII_pairs` requires). -/
def typeIIx (η : ℝ) (N : ℕ) : ℝ := min (η ^ 4 / (2 ^ 20 * (1 + Real.log N) ^ 18)) 1

/-- `typeIIx` is positive for `η > 0`. -/
theorem typeIIx_pos {η : ℝ} (hη : 0 < η) (N : ℕ) : 0 < typeIIx η N := by
  have hl : 0 < 1 + Real.log N := by
    have := Real.log_natCast_nonneg N
    linarith
  unfold typeIIx
  exact lt_min (by positivity) one_pos

/-- `typeIIx` is at most one. -/
theorem typeIIx_le_one (η : ℝ) (N : ℕ) : typeIIx η N ≤ 1 := min_le_right _ _

/-- `typeIIx` is at most the constant of the four-fold bound of the Vaughan decomposition. -/
theorem typeIIx_mul_le (η : ℝ) (N : ℕ) :
    typeIIx η N * (N : ℝ) ^ 2 ≤ η ^ 4 / (2 ^ 20 * (1 + Real.log N) ^ 18) * (N : ℝ) ^ 2 :=
  mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)

/-- **The Vaughan decomposition feeds the type II step and the extrapolation step.** The type II
disjunct of `vonMangoldt_sub_cramer_typeI_or_typeII` (`N < M³`, `L M < 4 N`, the four-fold
bound `η⁴ N² / (2²⁰ (1 + log N)¹⁸) ≤ fourFold φ (L/2, L] (M/2, M]`) together with `q³ ≤ N` gives
`type_two_extrapolation` with `x = typeIIx η N`; `1 ≤ M` and `q ≤ M` follow from `q³ ≤ N < M³`. -/
theorem type_two_extrapolation_of_C3 (deg : ℕ) (hdeg1 : 1 ≤ deg) (hdeg2 : deg ≤ 2) :
    ∃ (C₁ : ℕ) (C₂ : ℝ), 2 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ} (S : LengStart deg Q f p)
        {q : ℕ}, 1 ≤ q → (q : ℝ) ≤ Real.exp p → ∀ (r lo hi : ℤ) {N L M : ℕ} {η : ℝ},
        0 < η → q ^ 3 ≤ N → N < M ^ 3 → (L : ℝ) * M < 4 * N →
        η ^ 4 / (2 ^ 20 * (1 + Real.log N) ^ 18) * (N : ℝ) ^ 2 ≤
          fourFold (fun n : ℕ => typeISequence S.T q r lo hi (n : ℤ))
            (dyadicBlock L) (dyadicBlock M) →
        Real.exp (-(productNiltestBudget (p + 2) + 1)) ≤ typeIIx η N / 16 →
        ∀ {A : ℝ}, A ≤ typeIIx η N * M / (8 * q) →
        Real.exp ((productNiltestBudget (p + 2) + 1 + C₁) ^ C₁) ≤ A →
        Real.exp (C₂ * (((productNiltestBudget (p + 2) + 1 + C₁) ^ C₁) +
          Real.log (1 / (typeIIx η N / (32 * q)))) ^ 3) ≤ A →
        Real.exp (C₂ * (((productNiltestBudget (p + 2) + 1 + C₁) ^ C₁) +
          Real.log (1 / (typeIIx η N / (32 * q)))) ^ 3) ≤ L →
        ExtrapolatedSymbolFactorizationII S.D.filtration S.D.basis S.omega S.hF S.η
          (A * L / 2) (S.T.symbol S.D.basis S.omega S.hF)
          (C₂ * (((productNiltestBudget (p + 2) + 1 + C₁) ^ C₁) +
            Real.log (1 / (typeIIx η N / (32 * q))) + 1) ^ 4) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := type_two_extrapolation deg hdeg1 hdeg2
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro Q f p S q hq hqp r lo hi N L M η hη hq3 hM3 hLM hF hbias A hAx hA1 hA2 hL
  have hM1 : 1 ≤ M := by
    by_contra hM0
    have : M = 0 := by omega
    subst this
    simp at hM3
  have hqM : q ≤ M := by
    by_contra hlt
    have h1 : M < q := by omega
    have h2 : M ^ 3 < q ^ 3 := Nat.pow_lt_pow_left h1 (by norm_num)
    omega
  exact h S hq hqp r lo hi hM1 hqM hLM (typeIIx_pos hη N) (typeIIx_le_one η N) hbias
    ((typeIIx_mul_le η N).trans hF) hAx hA1 hA2 hL

end PrimeCarleson.Proof.Fplus31
