module

public import PrimeCarleson.Proof.Paper.P6a.Finite

/-!
# The leftover pairs `M(k) < Q ≤ k^{D₀}`

Source: main paper `p:red-var`, L1460–L1474.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The leftover pairs** (Source: main paper `p:red-var`, L1460–L1474): for `r > 2`, `p ≥ r'` and
every `D₀`, the set `{(k, 2^j) : k ≥ 1, M(k) < 2^j ≤ k^{D₀}}` is finite and the sum over it of
`‖V^r(∑_n f(x-n) w_Q(n) ψ_k(n) e(λ n) : λ)‖_{ℓ^p}` is `≤ C(D₀, p, r) ‖f‖_{ℓ^p}`. -/
theorem leftover_pairs (ψ : PsiData) {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) ≤ p) (D₀ : ℝ) :
    (leftoverSet D₀).Finite ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℤ →₀ ℂ,
      ∑ q ∈ (leftoverSet_finite D₀).toFinset,
          eLpNorm (varOp r (pairW ψ q.1 q.2) (⇑f)) (ENNReal.ofReal p) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  refine ⟨leftoverSet_finite D₀, ?_⟩
  have hrr : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent (by linarith)
  obtain ⟨C₀, hC₀, hcrude⟩ := crude_lambda_var_scale hr.le hrr
  have hr'1 : 1 ≤ r / (r - 1) := hrr.symm.lt.le
  have hp1 : 1 ≤ p := hr'1.trans hp
  have hr'0 : 0 < r / (r - 1) := by linarith
  set c : ℕ × ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal (C₀ * ((2 : ℝ) ^ q.1) ^ (1 / r)) *
    eLpNorm (pairW ψ q.1 q.2) (ENNReal.ofReal (r / (r - 1))) Measure.count with hc
  have hsupp : ∀ (q : ℕ × ℕ) (n : ℤ), (2 : ℝ) ^ q.1 < |(n : ℝ)| → pairW ψ q.1 q.2 n = 0 := by
    intro q n hn
    have : (2 : ℝ) ^ q.1 ≤ (n.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact hn.le
    simp [pairW, psiKz_eq_zero_of_ge ψ this]
  have hfin : ∀ q : ℕ × ℕ, c q ≠ ⊤ := by
    intro q
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have hS : ∀ n ∉ Finset.Icc (-(2 ^ q.1 : ℤ)) (2 ^ q.1), pairW ψ q.1 q.2 n = 0 := by
      intro n hn
      refine hsupp q n ?_
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      have : ((2 : ℤ) ^ q.1 : ℤ) < |n| := by
        rw [lt_abs]; rcases hn with h | h
        · right; omega
        · left; exact h
      have h2 : (((2 : ℤ) ^ q.1 : ℤ) : ℝ) < ((|n| : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h2
      exact_mod_cast h2
    rw [eLpNorm_count_eq_sum_of_support hS hr'0]
    refine (ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (ENNReal.sum_lt_top.2 fun n _ => ?_).ne).ne
    exact ENNReal.rpow_lt_top_of_nonneg hr'0.le enorm_ne_top
  have hsum : ∑ q ∈ (leftoverSet_finite D₀).toFinset, c q ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun q _ => (hfin q).lt_top).ne
  refine ⟨(∑ q ∈ (leftoverSet_finite D₀).toFinset, c q).toReal, ENNReal.toReal_nonneg, fun f => ?_⟩
  rw [ENNReal.ofReal_toReal hsum, Finset.sum_mul]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq' : q ∈ leftoverSet D₀ := (Set.Finite.mem_toFinset _).1 hq
  have hk1 : 1 ≤ q.1 := hq'.1
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ q.1 := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q.1 := pow_le_pow_right₀ (by norm_num) hk1
  have h3 := (hcrude ((2 : ℝ) ^ q.1) h2 (pairW ψ q.1 q.2) (⇑f) (hsupp q) p hp1).1 hp
  calc eLpNorm (varOp r (pairW ψ q.1 q.2) (⇑f)) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal (C₀ * ((2 : ℝ) ^ q.1) ^ (1 / r)) *
          eLpNorm (pairW ψ q.1 q.2) (ENNReal.ofReal (r / (r - 1))) Measure.count *
          eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := h3
    _ = c q * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := rfl

end PrimeCarleson.Proof.Paper
