module

public import PrimeCarleson.Proof.Fplus31.C2.IterationState
public import PrimeCarleson.Proof.Fplus31.C2.IterationBudget
public import PrimeCarleson.Proof.Fplus31.Comparison.Main
public import PrimeCarleson.Proof.Fplus31.TypeIII.Main
public import PrimeCarleson.Proof.Fplus31.Cramer.Approx

/-!
# The iteration, the regime and the type I / type II dichotomy for a state

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1).
`normLam N` is the 1-bounded function `(Λ - Λ_{C,w}) / (3 log N)` of the inverse theorem,
`w = cramerLevel N`. `Reg N P` is the numerical regime of a stage at the
level `P`: `log N ≥ max (12, 6 P)` (so `e^P ≤ N^{1/6}`), the bound `‖normLam N‖ ≤ 1` and the Brun
truncation with a level `k` (`BrunOK N P`: `w^{3k} ≤ N²` and the numeric `L¹` bound of
`cramer_brun_L1_Icc` below `3 log N · e^{-P} N / 8`). `c3_dichotomy` is the Vaughan decomposition
applied to the state: for a niltest correlating with `normLam N` on a progression at the level
`e^{-p}`, either the type I output (many dilations with a large sum) or the type II output (the
four-fold bound).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration Finset

/-- The function `(Λ - Λ_{C,w}) / (3 log N)` of the inverse theorem, `w = cramerLevel N`. -/
def normLam (N : ℕ) (n : ℤ) : ℂ :=
  (((3 * Real.log N)⁻¹ : ℝ) : ℂ) *
    (((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
      ((cramerModel (cramerLevel N) n : ℝ) : ℂ))

/-- **The Brun truncation of a stage at the level `P`**: a level `k` with `w^{3k} ≤ N²` and the
numeric `L¹` bound of the Brun truncation below `3 log N · e^{-P} N / 8` (`w = cramerLevel N`). -/
def BrunOK (N : ℕ) (P : ℝ) : Prop :=
  ∃ k : ℕ, 2 ≤ cramerLevel N ∧ cramerLevel N ≤ N ∧ (cramerLevel N ^ k) ^ 3 ≤ N ^ 2 ∧
    Real.exp 5 * Real.log (cramerLevel N) *
      ((N : ℝ) * (Real.exp 1 * (Real.log (Real.log (cramerLevel N)) + 4) /
          ((k + 1 : ℕ) : ℝ)) ^ (k + 1) + ((cramerLevel N : ℕ) : ℝ) ^ (k + 1)) ≤
      3 * Real.log N * Real.exp (-P) * N / 8

/-- `BrunOK` is antitone in the level. -/
theorem BrunOK.mono {N : ℕ} {P P' : ℝ} (h : BrunOK N P') (hP : P ≤ P') : BrunOK N P := by
  obtain ⟨k, h1, h2, h3, h4⟩ := h
  refine ⟨k, h1, h2, h3, h4.trans ?_⟩
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have : Real.exp (-P') ≤ Real.exp (-P) := Real.exp_le_exp.mpr (by linarith)
  have h5 : 3 * Real.log N * Real.exp (-P') ≤ 3 * Real.log N * Real.exp (-P) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  have h6 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_right h5 h6
  linarith

/-- The function `normLam N` is bounded by one on `[1, N]`. -/
def NormOK (N : ℕ) : Prop := ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖normLam N n‖ ≤ 1

/-- **The regime of a stage at the level `P`**: `log N ≥ max (12, 6 P)`, the Brun truncation and
the bound `‖normLam N‖ ≤ 1` on `[1, N]`. -/
def Reg (N : ℕ) (P : ℝ) : Prop :=
  12 ≤ Real.log N ∧ 6 * P ≤ Real.log N ∧ BrunOK N P ∧ NormOK N

/-- `Reg` is antitone in the level. -/
theorem Reg.mono {N : ℕ} {P P' : ℝ} (h : Reg N P') (hP : P ≤ P') : Reg N P :=
  ⟨h.1, by linarith [h.2.1], h.2.2.1.mono hP, h.2.2.2⟩

/-- `log N ≥ 12` gives `N ≥ 3`. -/
theorem three_le_of_twelve_le_log {N : ℕ} (h : 12 ≤ Real.log N) : 3 ≤ N := by
  have hN : (0 : ℝ) < N := by
    by_contra hc
    have : (N : ℝ) = 0 := le_antisymm (not_lt.mp hc) (Nat.cast_nonneg N)
    rw [this, Real.log_zero] at h
    linarith
  have h1 : Real.exp 12 ≤ N := (Real.le_log_iff_exp_le hN).mp h
  have h2 : (13 : ℝ) ≤ Real.exp 12 := by linarith [Real.add_one_le_exp (12 : ℝ)]
  have : (3 : ℝ) ≤ N := by linarith
  exact_mod_cast this

/-- The sum against `normLam N` over a progression `⊆ [1, N]`, as the sum over `[1, N]` of the
Vaughan decomposition integrand against `typeISequence`:
`‖∑ (Λ - Λ_C) φ‖ = 3 log N ‖∑_P normLam · star T‖`. -/
theorem norm_c3_sum_eq {N : ℕ} {D : Type*} [LieRing D] [LieAlgebra ℚ D] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] D)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] D)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D)] [T2Space (ℝ ⊗[ℚ] D)]
    {M : RationalFilteredNilmanifold D s d} (T : M.Niltest (fun _ : Unit => 1))
    {q : ℕ} {r lo hi : ℤ} (hlo : 1 ≤ lo) (hhi : hi ≤ N) (hlog : 0 < Real.log N) :
    ‖∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.vonMangoldt n - cramerModel (cramerLevel N) (n : ℤ) : ℝ) : ℂ) *
          typeISequence T q r lo hi n‖ =
      3 * Real.log N *
        ‖∑ x ∈ apInt q r lo hi, normLam N x * star (T.eval fun _ => x)‖ := by
  set g : ℤ → ℂ := fun z => (((ArithmeticFunction.vonMangoldt z.toNat : ℝ) : ℂ) -
    ((cramerModel (cramerLevel N) z : ℝ) : ℂ)) with hg
  have h1 : ∑ n ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.vonMangoldt n - cramerModel (cramerLevel N) (n : ℤ) : ℝ) : ℂ) *
        typeISequence T q r lo hi n =
      ∑ z ∈ Finset.Icc (1 : ℤ) N, g z * typeISequence T q r lo hi z := by
    rw [← sum_Icc_natCast_eq_int (fun z => g z * typeISequence T q r lo hi z) N]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [hg]
  have h2 : ∑ z ∈ Finset.Icc (1 : ℤ) N, g z * typeISequence T q r lo hi z =
      ∑ x ∈ apInt q r lo hi, g x * star (T.eval fun _ => x) :=
    sum_Icc_progIndicator_mul q r lo hi hlo hhi g (fun x => star (T.eval fun _ => x))
  have h3 : ∑ x ∈ apInt q r lo hi, g x * star (T.eval fun _ => x) =
      ((3 * Real.log N : ℝ) : ℂ) *
        ∑ x ∈ apInt q r lo hi, normLam N x * star (T.eval fun _ => x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hci : ((3 * Real.log N : ℝ) : ℂ) * (((3 * Real.log N)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity), Complex.ofReal_one]
    have hn : normLam N x = (((3 * Real.log N)⁻¹ : ℝ) : ℂ) * g x := rfl
    rw [hn]
    calc g x * star (T.eval fun _ => x) =
        (((3 * Real.log N : ℝ) : ℂ) * (((3 * Real.log N)⁻¹ : ℝ) : ℂ)) * g x *
          star (T.eval fun _ => x) := by rw [hci, one_mul]
      _ = _ := by ring
  rw [h1, h2, h3, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- **The Vaughan decomposition for a state** (with the numeric Brun bound): for a niltest
correlating with `normLam N` on a progression `⊆ [1, N]` in the sum form `N e^{-p}`, and a level
`P ≥ p` in the regime `Reg N P`, either the type I output (with `η = 3 log N e^{-p}`) or the type II
output (the four-fold bound) holds for `φ = typeISequence S.T q r lo hi`. -/
theorem c3_dichotomy {s : ℕ} {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
    (S : LengStart (s + 1) Q f p) {N : ℕ} {q : ℕ} {r lo hi : ℤ} (hAP : APInv N p q r lo hi)
    {P : ℝ} (hpP : p ≤ P) (hReg : Reg N P)
    (hsum : (N : ℝ) * Real.exp (-p) ≤
      ‖∑ x ∈ apInt q r lo hi, normLam N x * star (S.T.eval fun _ => x)‖)
    {η : ℝ} (hη : η = 3 * Real.log N * Real.exp (-p)) :
    (∃ N' ≤ N, ∃ L : ℕ, 1 ≤ L ∧ L ^ 3 ≤ N ^ 2 ∧ ∃ Λ' : Finset ℕ,
        (∀ ℓ ∈ Λ', (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) ∧
        η / (2 ^ 13 * (1 + Real.log N) ^ 3) * L ≤ Λ'.card ∧
        ∀ ℓ ∈ Λ', η / (2 ^ 13 * (1 + Real.log N) ^ 3) * ((N : ℝ) / L) ≤
          ‖∑ n ∈ Icc 1 ⌊(N' : ℝ) / ℓ⌋₊, typeISequence S.T q r lo hi ((ℓ : ℤ) * n)‖) ∨
    (∃ L M : ℕ, N < L ^ 3 ∧ L ^ 3 ≤ N ^ 2 ∧ N < M ^ 3 ∧ M ^ 3 ≤ N ^ 2 ∧
        η / (16 * (1 + Real.log N) ^ 5) * N ≤ (L : ℝ) * M ∧ (L : ℝ) * M < 4 * N ∧
        η ^ 4 / (2 ^ 20 * (1 + Real.log N) ^ 18) * (N : ℝ) ^ 2 ≤
          fourFold (fun n : ℕ => typeISequence S.T q r lo hi (n : ℤ)) (dyadicBlock L)
            (dyadicBlock M)) := by
  obtain ⟨hU12, hU6, ⟨k, hw2, hwN, hlevel, hbrun⟩, -⟩ := hReg
  have hN3 := three_le_of_twelve_le_log hU12
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set U := Real.log N with hU
  have hlog : 0 < U := by linarith
  have hp0 : 0 ≤ p := S.nonneg
  have hpU : p ≤ U / 6 := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hsmall : 8 * U * (N : ℝ) ^ ((3 : ℝ)⁻¹) ≤ η * N := by
    have hNe : (N : ℝ) = Real.exp U := (Real.exp_log hNpos).symm
    have hrp : (N : ℝ) ^ ((3 : ℝ)⁻¹) = Real.exp (U / 3) := by
      rw [Real.rpow_def_of_pos hNpos]; congr 1
    have h1 : (8 : ℝ) ≤ 3 * Real.exp (2 * U / 3 - p) := by
      have h6 : (6 : ℝ) ≤ 2 * U / 3 - p := by linarith
      have := Real.add_one_le_exp (2 * U / 3 - p)
      linarith
    have h2 : Real.exp (2 * U / 3 - p) * Real.exp (U / 3) = Real.exp (-p) * Real.exp U := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [hrp, hη]
    rw [hNe]
    calc 8 * U * Real.exp (U / 3) ≤ 3 * Real.exp (2 * U / 3 - p) * U * Real.exp (U / 3) := by
          have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ U * Real.exp (U / 3))
          linarith
      _ = 3 * U * (Real.exp (2 * U / 3 - p) * Real.exp (U / 3)) := by ring
      _ = 3 * U * Real.exp (-p) * Real.exp U := by rw [h2]; ring
  have hbrun' : Real.exp 5 * Real.log (cramerLevel N) *
      ((N : ℝ) * (Real.exp 1 * (Real.log (Real.log (cramerLevel N)) + 4) /
          ((k + 1 : ℕ) : ℝ)) ^ (k + 1) + ((cramerLevel N : ℕ) : ℝ) ^ (k + 1)) ≤ η * N / 8 := by
    refine hbrun.trans ?_
    rw [hη]
    have : Real.exp (-P) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
    have h5 : 3 * U * Real.exp (-P) ≤ 3 * U * Real.exp (-p) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have := mul_le_mul_of_nonneg_right h5 hNpos.le
    linarith
  have hT : (S.T.normBound : ℝ) ≤ 1 := by exact_mod_cast S.norm_le
  have hφ := norm_typeISequence_le S.T hT q r lo hi
  have hφN : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → typeISequence S.T q r lo hi n = 0 := by
    intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    apply typeISequence_eq_zero
    have := hAP.one_le_lo
    have := hAP.hi_le
    omega
  have hcorr : η * N ≤ ‖∑ n ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.vonMangoldt n - cramerModel (cramerLevel N) (n : ℤ) : ℝ) : ℂ) *
        typeISequence S.T q r lo hi n‖ := by
    rw [norm_c3_sum_eq S.T hAP.one_le_lo hAP.hi_le hlog, hη]
    calc 3 * U * Real.exp (-p) * N = 3 * U * ((N : ℝ) * Real.exp (-p)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  exact vonMangoldt_sub_cramer_typeI_or_typeII_of_brun (N := N) (w := cramerLevel N) (k := k)
    (by omega) hw2 hwN hlevel hη0 hsmall hbrun' (typeISequence S.T q r lo hi) hφ hφN hcorr

end PrimeCarleson.Proof.Fplus31
