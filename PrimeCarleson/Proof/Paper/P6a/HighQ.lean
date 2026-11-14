module

public import PrimeCarleson.Proof.Paper.P6a.Moments
public import PrimeCarleson.Proof.Paper.P6a.Hyps
public import PrimeCarleson.Proof.Paper.P6a.Interp
public import PrimeCarleson.Proof.FplusProp21.Application
public import PrimeCarleson.Proof.Paper.P6a.Series
public import PrimeCarleson.Proof.KMTT.BlockMoment

/-!
# The high-denominator term of the proof of `p:red-var`

Source: main paper `p:red-var`, L1411–L1458: `e:highQ-var-L2-red` (the `ℓ²` bound from
`e:local-U3-var-red`, `[F+, Proposition 2.1]`, and the moment `‖w_Q‖_{L²([2^k])} ≲ Q^{o(1)}` of
[FKT1] Lemma 3.1), the crude `ℓ^s` bound (L1434–L1456). The summed bound (L1456–L1458: interpolation
and the sum over `k` and the dyadic `Q` with `k^{D₀} < Q ≤ M(k)`, for `D₀` large) is
`highQ_sum_param` of `Main/Interp.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **`e:highQ-var-L2-red`** (L1421-L1432): for every `ε > 0`, `k ≥ 1` and dyadic `Q = 2^j ≤ M(k)`,
`‖V^r(∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n) : λ)‖_{ℓ²} ≤ C_{r,ε} k^{2/r} Q^{-(3/8)(1-2/r) + ε} ‖f‖_{ℓ²}`
(the paper's `Q^{-(3/8)(1-2/r)+o(1)}`). -/
theorem highQ_var_L2_red (ψ : PsiData) {r : ℝ} (hr : 2 < r) (hLoc : LocalU3VarRed ψ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k j : ℕ), 1 ≤ k → (2 : ℝ) ^ j ≤ cutoffM k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (pairW ψ k j) (⇑f)) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (2 / r) *
            ((2 : ℝ) ^ j) ^ (-(3 / 8) * (1 - 2 / r) + ε)) *
          eLpNorm (⇑f) (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C_L, hCL0, hL⟩ := hLoc
  obtain ⟨C_U, hU⟩ := FplusProp21.exists_gowersNormInterval_blockWeight_Ioc_two_pow_le hε
  obtain ⟨C₂, hC₂0, hC₂⟩ := wQ_moment_L2
  obtain ⟨C_ε, hCε0, hCε⟩ := KMTT.exists_pow_log_le_rpow hε
  have ha : 0 < 1 - 2 / r := by
    rw [sub_pos, div_lt_one (by linarith)]; exact hr
  have hb : 0 < 2 / r := by positivity
  refine ⟨C_L * |C_U| ^ (1 - 2 / r) * (C₂ * C_ε) ^ (2 / r), by positivity, fun k j hk hj f => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set N : ℕ+ := ⟨2 ^ k, by positivity⟩ with hNdef
  have hN : (N : ℕ) = 2 ^ k := rfl
  have hev : ∀ n, wQ (2 ^ j) (-n) = wQ (2 ^ j) n := fun n => wQ_neg _ n
  refine (hL k N hk hN (wQ (2 ^ j)) hev f).trans ?_
  have hQ : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hU1 : gowersNormInterval 3 N (wQ (2 ^ j)) ≤
      |C_U| * ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + ε) := by
    have := hU k N hN j hj
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hM1 : lpNormOn 2 (bracket N) (wQ (2 ^ j)) ≤ C₂ * C_ε * ((2 : ℝ) ^ j) ^ ε := by
    have h1 := hC₂ (2 ^ j) N Nat.one_le_two_pow
    have h2 := hCε ((2 : ℝ) ^ j) hQ1
    have hc : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; rfl
    rw [hc] at h1
    calc _ ≤ C₂ * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3 := h1
      _ ≤ C₂ * (C_ε * ((2 : ℝ) ^ j) ^ ε) := mul_le_mul_of_nonneg_left h2 hC₂0
      _ = _ := by ring
  have hU0 : 0 ≤ gowersNormInterval 3 N (wQ (2 ^ j)) := by
    rw [gowersNormInterval_eq_gowersNormOn]; exact gowersNormOn_nonneg _ _ _
  have hM0 := lpNormOn_nonneg 2 (bracket N) (wQ (2 ^ j))
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc C_L * (k : ℝ) ^ (2 / r) * gowersNormInterval 3 N (wQ (2 ^ j)) ^ (1 - 2 / r) *
        lpNormOn 2 (bracket N) (wQ (2 ^ j)) ^ (2 / r)
      ≤ C_L * (k : ℝ) ^ (2 / r) * (|C_U| * ((2 : ℝ) ^ j) ^ (-(3 : ℝ) / 8 + ε)) ^ (1 - 2 / r) *
          (C₂ * C_ε * ((2 : ℝ) ^ j) ^ ε) ^ (2 / r) := by gcongr
    _ = C_L * |C_U| ^ (1 - 2 / r) * (C₂ * C_ε) ^ (2 / r) * (k : ℝ) ^ (2 / r) *
          ((2 : ℝ) ^ j) ^ (-(3 / 8) * (1 - 2 / r) + ε) := by
        rw [Real.mul_rpow (abs_nonneg _) (by positivity), Real.mul_rpow (by positivity)
          (by positivity), ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le]
        have : ((2 : ℝ) ^ j) ^ (-(3 / 8) * (1 - 2 / r) + ε) =
            ((2 : ℝ) ^ j) ^ ((-(3 : ℝ) / 8 + ε) * (1 - 2 / r)) *
              ((2 : ℝ) ^ j) ^ (ε * (2 / r)) := by
          rw [← Real.rpow_add hQ]; congr 1; ring
        rw [this]; ring

/-- **The crude `ℓ^s` bound** (Source: main paper `p:red-var`, L1434–L1456): for every `s ≥ r'`,
`k ≥ 1` and `Q = 2^j`,
`‖V^r(∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n) : λ)‖_{ℓ^s} ≤ C_r (1 + log Q)^3 ‖f‖_{ℓ^s}` (`≲ Q^{o(1)}`). -/
theorem highQ_crude (ψ : PsiData) {r : ℝ} (hr : 2 < r) {s : ℝ} (hs : r / (r - 1) ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k j : ℕ), 1 ≤ k → ∀ f : ℤ →₀ ℂ,
      eLpNorm (varOp r (pairW ψ k j) (⇑f)) (ENNReal.ofReal s) Measure.count ≤
        ENNReal.ofReal (C * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3) *
          eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  obtain ⟨C_c, hCc0, hc⟩ := crude_piece_le ψ hr
  obtain ⟨C₂, hC₂0, hC₂⟩ := wQ_moment_L2
  have hr1 : 0 < r - 1 := by linarith
  have hr'1 : 1 ≤ r / (r - 1) := by rw [le_div_iff₀ hr1]; linarith
  have hr'2 : r / (r - 1) ≤ 2 := by rw [div_le_iff₀ hr1]; linarith
  refine ⟨C_c * C₂, by positivity, fun k j hk f => ?_⟩
  set N : ℕ+ := ⟨2 ^ k, by positivity⟩ with hNdef
  have hN : (N : ℕ) = 2 ^ k := rfl
  refine (hc k N hk hN (wQ (2 ^ j)) (fun n => wQ_neg _ n) s hs f).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have h1 := lpNormOn_le_two hr'1 hr'2 (bracket_nonempty N) (wQ (2 ^ j))
  have h2 := hC₂ (2 ^ j) N Nat.one_le_two_pow
  have hc2 : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; rfl
  rw [hc2] at h2
  calc C_c * lpNormOn (r / (r - 1)) (bracket N) (wQ (2 ^ j))
      ≤ C_c * (C₂ * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hCc0
    _ = C_c * C₂ * (1 + Real.log ((2 : ℝ) ^ j)) ^ 3 := by ring

end PrimeCarleson.Proof.Paper
