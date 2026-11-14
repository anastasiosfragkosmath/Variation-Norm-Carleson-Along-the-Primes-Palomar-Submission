module

public import PrimeCarleson.Proof.Fplus31.C2.CMainBrun
public import PrimeCarleson.Proof.Fplus31.PNTSW.Main
public import PrimeCarleson.Proof.Fplus31.ZeroFree.Main
public import OAI.NumberTheory.SiegelZeros.Conclusions.Theorem

/-!
# The Cramér-model comparison, the facts at large `N`

Part of the final parameters of the iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1).
For `u = (log N)^{1/10} ≥ 3` (`N` large):

* `cramerLevel_bounds`: `2 ≤ w = cramerLevel N ≤ 2 e^u` and `e^u / 2 ≤ w ≤ e^u + 1`;
* `normOK_of_large`: `‖(Λ - Λ_{C,w}) / (3 log N)‖ ≤ 1` on `[1, N]`;
* `brunOK_of_large`: `BrunOK N P` for `P ≥ 0` with `P² ≤ log N` (`brun_params`);
* `termOK_of_large`: `TermOK N P` for `P < (log log N)^{K'}` (the prime number theorem in
  progressions, on the classical zero-free region and with no Siegel zeros:
  `PNTSW.c5_terminal_sw` with `ZeroFree.classicalZeroFreeRegion` and the `openai/math`
  Landau–Siegel theorem `exists_absolute_real_zero_gap`).
-/

@[expose] public noncomputable section

open ArithmeticFunction Filter

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `log N = u^{10}` for `u = (log N)^{1/10}`. -/
theorem log_eq_pow_ten {N : ℕ} {u : ℝ} (hu : u = Real.log N ^ ((1 : ℝ) / 10)) :
    Real.log N = u ^ 10 := by
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hlog0]
  norm_num

/-- The bounds on `w = cramerLevel N` for `u = (log N)^{1/10} ≥ 0`. -/
theorem cramerLevel_bounds (N : ℕ) {u : ℝ} (hu : u = Real.log N ^ ((1 : ℝ) / 10)) (hu0 : 0 ≤ u) :
    2 ≤ cramerLevel N ∧ (cramerLevel N : ℝ) ≤ 2 * Real.exp u ∧
      Real.exp u / 2 ≤ (cramerLevel N : ℝ) ∧ (cramerLevel N : ℝ) ≤ Real.exp u + 1 := by
  have hw : (cramerLevel N : ℝ) = (2 : ℝ) ^ Nat.log 2 ⌊Real.exp u⌋₊ + 1 := by
    unfold cramerLevel
    rw [← hu]
    simp
  obtain ⟨h1, h2, h3, h4⟩ := cramerLevel_facts hu0
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 : ℝ) ≤ (cramerLevel N : ℝ) := by rw [hw]; exact h3
    exact_mod_cast this
  · rw [hw]; exact h4
  · rw [hw]
    have : Real.exp u < 2 * (2 : ℝ) ^ Nat.log 2 ⌊Real.exp u⌋₊ := by
      have := h2
      rw [pow_succ] at this
      linarith
    linarith
  · rw [hw]; linarith

/-- **`normLam N` is bounded by one on `[1, N]`** for `u = (log N)^{1/10} ≥ 3`. -/
theorem normOK_of_large {N : ℕ} {u : ℝ} (hu : u = Real.log N ^ ((1 : ℝ) / 10)) (hu3 : 3 ≤ u) :
    NormOK N := by
  intro n hn
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  obtain ⟨hw2, hw, -, -⟩ := cramerLevel_bounds N hu (by linarith)
  have hU : Real.log N = u ^ 10 := log_eq_pow_ten hu
  have hU0 : 0 < Real.log N := by rw [hU]; positivity
  set w := cramerLevel N with hwdef
  have hw2R : (2 : ℝ) ≤ w := by exact_mod_cast hw2
  have hwpos : (0 : ℝ) < w := by linarith
  have hlw : Real.log w ≤ 2 * u := by
    have h1 : Real.log w ≤ Real.log (2 * Real.exp u) := Real.log_le_log hwpos hw
    rw [Real.log_mul (by norm_num) (Real.exp_pos u).ne', Real.log_exp] at h1
    have := Real.log_two_lt_d9
    linarith
  have hu0 : 0 ≤ u := by linarith
  have hu9 : (19683 : ℝ) ≤ u ^ 9 := by
    calc (19683 : ℝ) = 3 ^ 9 := by norm_num
      _ ≤ u ^ 9 := pow_le_pow_left₀ (by norm_num) hu3 9
  have he5 := Real.exp_one_lt_d9
  have he5' : Real.exp 5 ≤ 149 := by
    have : Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (Real.exp 1) ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le he5.le 5
      _ ≤ 149 := by norm_num
  have hlogn : Real.log (n.toNat : ℝ) ≤ Real.log N := by
    have hn0 : (1 : ℤ) ≤ n := hn1
    have : (1 : ℝ) ≤ (n.toNat : ℝ) := by
      have : 1 ≤ n.toNat := by omega
      exact_mod_cast this
    refine Real.log_le_log (by linarith) ?_
    have : n.toNat ≤ N := by omega
    exact_mod_cast this
  have hvm : (vonMangoldt n.toNat : ℝ) ≤ Real.log N := vonMangoldt_le_log.trans hlogn
  have hvm0 : (0 : ℝ) ≤ vonMangoldt n.toNat := vonMangoldt_nonneg
  have hc0 := cramerModel_nonneg w n
  have hc1 : cramerModel w n ≤ Real.exp 5 * Real.log w := cramerModel_le w hw2 n
  have hc2 : cramerModel w n ≤ 3 * Real.log N := by
    have : Real.exp 5 * Real.log w ≤ 149 * (2 * u) := by
      have hl0 : 0 ≤ Real.log w := Real.log_nonneg (by linarith)
      exact mul_le_mul he5' hlw hl0 (by norm_num)
    rw [hU]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < u) 1]
  have hdiff : |(vonMangoldt n.toNat : ℝ) - cramerModel w n| ≤ 3 * Real.log N := by
    rw [abs_le]
    constructor <;> linarith
  unfold normLam
  rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

/-- **`BrunOK N P`** for `u = (log N)^{1/10} ≥ 3` and `0 ≤ P`, `P² ≤ log N`. -/
theorem brunOK_of_large {N : ℕ} {u P : ℝ} (hu : u = Real.log N ^ ((1 : ℝ) / 10)) (hu3 : 3 ≤ u)
    (hP0 : 0 ≤ P) (hP : P ^ 2 ≤ Real.log N) : BrunOK N P := by
  obtain ⟨hw2, hw, -, -⟩ := cramerLevel_bounds N hu (by linarith)
  have hU : Real.log N = u ^ 10 := log_eq_pow_ten hu
  have hNpos : (0 : ℝ) < N := by
    by_contra h
    have h0 : (N : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg N)
    rw [h0, Real.log_zero] at hU
    have : (0 : ℝ) < u ^ 10 := by positivity
    linarith
  have hN : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
  obtain ⟨k, hwN, hlev, hbr⟩ := brun_params (N := N) (w := cramerLevel N) (u := u) (P := P)
    (U := Real.log N) hU hu3 hP0 hP hN hw2 hw
  exact ⟨k, hw2, hwN, hlev, hbr⟩

/-- **`TermOK N P`** for `N` large and `P < (log log N)^{K'}` (the prime number theorem in
progressions, `PNTSW.c5_terminal_sw`). -/
theorem termOK_of_large (K' : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ P : ℝ, P < Real.log (Real.log N) ^ K' → TermOK N P := by
  obtain ⟨N₀, h⟩ := PNTSW.c5_terminal_sw ZeroFree.classicalZeroFreeRegion
    OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap K'
  refine ⟨max N₀ 3, fun N hN P hP => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hU1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  set u : ℝ := Real.log N ^ ((1 : ℝ) / 10) with hu
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨-, -, hw1, hw2⟩ := cramerLevel_bounds N hu hu0
  intro q r lo hi hq hlo hhi
  have hq' : 1 ≤ q := hq
  by_cases hlh : lo ≤ hi
  · have hset : apInt q r lo hi = apSet q r (lo - 1).toNat hi.toNat := by
      ext x
      simp only [mem_apInt, apSet, Finset.mem_filter, Finset.mem_Ioc]
      have h1 : (((lo - 1).toNat : ℕ) : ℤ) = lo - 1 := Int.toNat_of_nonneg (by omega)
      have h2 : ((hi.toNat : ℕ) : ℤ) = hi := Int.toNat_of_nonneg (by omega)
      rw [h1, h2]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨⟨by omega, b⟩, c⟩
      · rintro ⟨⟨a, b⟩, c⟩; exact ⟨by omega, b, c⟩
    have hc5 := h N hN0 (cramerLevel N) hw1 hw2 q hq' r
      (lo - 1).toNat hi.toNat (by omega) (by omega)
    have hsum : ∑ x ∈ apInt q r lo hi, normLam N x =
        (((3 * Real.log N)⁻¹ : ℝ) : ℂ) *
          ((∑ n ∈ apSet q r (lo - 1).toNat hi.toNat,
            ((vonMangoldt n.toNat : ℝ) - cramerModel (cramerLevel N) n) : ℝ) : ℂ) := by
      rw [hset, Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold normLam
      push_cast
      rfl
    rw [hsum, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.norm_eq_abs]
    have hinv : (3 * Real.log N)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]; linarith
    calc (3 * Real.log N)⁻¹ * |∑ n ∈ apSet q r (lo - 1).toNat hi.toNat,
          ((vonMangoldt n.toNat : ℝ) - cramerModel (cramerLevel N) n)| ≤
        1 * (N * Real.exp (-(Real.log (Real.log N) ^ K'))) :=
          mul_le_mul hinv hc5 (abs_nonneg _) zero_le_one
      _ < N * Real.exp (-P) := by
          rw [one_mul]
          exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) hNpos
  · have : apInt q r lo hi = ∅ := by
      ext x
      simp only [mem_apInt, Finset.notMem_empty, iff_false]
      omega
    rw [this]
    simp only [Finset.sum_empty, norm_zero]
    positivity

end PrimeCarleson.Proof.Fplus31
