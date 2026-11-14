module

public import PrimeCarleson.Proof.Fplus31.C2.TypeI
public import PrimeCarleson.Proof.Fplus31.TypeIII.Main

/-!
# The type I sequence of a progression

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
Vaughan decomposition (`TypeIII/Main.lean`, `vonMangoldt_sub_cramer_typeI_or_typeII`) is applied to
`φ = typeISequence T q r lo hi = 1_P · star (T.eval)` for the progression
`P = {n ∈ [lo, hi] : n ≡ r (q)}`, and needs `φ` bounded by one and supported on `[lo, hi]`. This
file proves these two facts, for the indicator of the progression (`norm_progIndicator_le`,
`progIndicator_eq_zero`) and for `φ` (`norm_typeISequence_le`, `typeISequence_eq_zero`).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The indicator of a progression is bounded by one. -/
theorem norm_progIndicator_le (q : ℕ) (r lo hi n : ℤ) : ‖progIndicator q r lo hi n‖ ≤ 1 := by
  unfold progIndicator
  split_ifs <;> simp

/-- The indicator of a progression vanishes outside `[lo, hi]`. -/
theorem progIndicator_eq_zero {q : ℕ} {r lo hi n : ℤ} (h : n < lo ∨ hi < n) :
    progIndicator q r lo hi n = 0 := by
  unfold progIndicator
  have hn : ¬ (lo ≤ n ∧ n ≤ hi ∧ n ≡ r [ZMOD q]) := by
    rintro ⟨h1, h2, -⟩
    omega
  rw [ite_eq_right hn]

section Niltest

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

/-- `φ = 1_P · star (T.eval)` is bounded by one. -/
theorem norm_typeISequence_le (T : D.Niltest (fun _ : Unit => 1)) (hT : (T.normBound : ℝ) ≤ 1)
    (q : ℕ) (r lo hi n : ℤ) : ‖typeISequence T q r lo hi n‖ ≤ 1 := by
  unfold typeISequence
  rw [norm_mul, norm_star]
  calc ‖progIndicator q r lo hi n‖ * ‖T.eval fun _ => n‖ ≤ 1 * 1 :=
        mul_le_mul (norm_progIndicator_le _ _ _ _ _) ((T.norm_eval_le _).trans hT)
          (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- `φ = 1_P · star (T.eval)` vanishes outside `[lo, hi]`. -/
theorem typeISequence_eq_zero (T : D.Niltest (fun _ : Unit => 1)) {q : ℕ} {r lo hi : ℤ}
    {n : ℤ} (h : n < lo ∨ hi < n) : typeISequence T q r lo hi n = 0 := by
  unfold typeISequence
  rw [progIndicator_eq_zero h, zero_mul]

end Niltest

end PrimeCarleson.Proof.Fplus31
