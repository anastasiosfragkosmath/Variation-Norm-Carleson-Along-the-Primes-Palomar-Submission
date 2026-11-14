module

public import PrimeCarleson.Proof.Paper.P6a.Basic

/-!
# The leftover pairs of the main-term split are finite

Source: main paper `p:red-var`, L1460–L1474: the set `{(k, Q) : M(k) < Q ≤ k^{D₀}}`, `Q` dyadic, is
finite, because `exp(k^{1/10})` outgrows every power of `k`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- `k^{D₀} ≤ M(k)` for all large `k`: `exp(k^{1/10})` outgrows every power of `k`. -/
theorem eventually_rpow_le_cutoffM (D₀ : ℝ) :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → (k : ℝ) ^ D₀ ≤ cutoffM k := by
  set c : ℝ := 20 * max D₀ 0 + 1 with hc
  have hc1 : 1 ≤ c := by have := le_max_right D₀ 0; rw [hc]; linarith
  refine ⟨⌈c ^ (20 : ℕ)⌉₊ + 1, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (0 : ℝ) < k := by linarith
  have hck : c ^ (20 : ℕ) ≤ k := by
    have : (⌈c ^ (20 : ℕ)⌉₊ : ℝ) ≤ k := by exact_mod_cast (by omega : ⌈c ^ (20 : ℕ)⌉₊ ≤ k)
    exact (Nat.le_ceil _).trans this
  -- c ≤ k^(1/20)
  have hck2 : c ≤ (k : ℝ) ^ ((1 : ℝ) / 20) := by
    have h := Real.rpow_le_rpow (by positivity) hck (by norm_num : (0 : ℝ) ≤ 1 / 20)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at h
    simpa using h
  have hlog : Real.log k ≤ (k : ℝ) ^ ((1 : ℝ) / 20) / (1 / 20) :=
    Real.log_le_rpow_div hk0.le (by norm_num)
  have hpow : (k : ℝ) ^ ((1 : ℝ) / 10) = (k : ℝ) ^ ((1 : ℝ) / 20) * (k : ℝ) ^ ((1 : ℝ) / 20) := by
    rw [← Real.rpow_add hk0]; norm_num
  unfold cutoffM
  rw [Real.rpow_def_of_pos hk0]
  refine Real.exp_le_exp.2 ?_
  have hD : D₀ ≤ max D₀ 0 := le_max_left _ _
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk1
  have h20 : 20 * max D₀ 0 ≤ (k : ℝ) ^ ((1 : ℝ) / 20) := by linarith
  have hy0 : 0 ≤ (k : ℝ) ^ ((1 : ℝ) / 20) := by positivity
  calc Real.log k * D₀ ≤ Real.log k * max D₀ 0 := mul_le_mul_of_nonneg_left hD hlog0
    _ ≤ ((k : ℝ) ^ ((1 : ℝ) / 20) / (1 / 20)) * max D₀ 0 :=
        mul_le_mul_of_nonneg_right hlog (le_max_right _ _)
    _ = (k : ℝ) ^ ((1 : ℝ) / 20) * (20 * max D₀ 0) := by ring
    _ ≤ (k : ℝ) ^ ((1 : ℝ) / 20) * (k : ℝ) ^ ((1 : ℝ) / 20) :=
        mul_le_mul_of_nonneg_left h20 hy0
    _ = (k : ℝ) ^ ((1 : ℝ) / 10) := hpow.symm

/-- **The leftover pairs are finite** (Source: main paper `p:red-var`, L1460–L1474). -/
theorem leftoverSet_finite (D₀ : ℝ) : (leftoverSet D₀).Finite := by
  obtain ⟨K₀, hK₀⟩ := eventually_rpow_le_cutoffM D₀
  set J₀ : ℕ := ⌈(max (K₀ : ℝ) 1) ^ (max D₀ 0)⌉₊ + 1 with hJ₀
  refine ((Set.finite_Iio K₀).prod (Set.finite_Iio J₀)).subset ?_
  rintro ⟨k, j⟩ ⟨hk1, hM, hD⟩
  simp only [Set.mem_prod, Set.mem_Iio]
  have hk : k < K₀ := by
    by_contra h
    exact absurd (hK₀ k (not_lt.1 h)) (not_le.2 (lt_of_lt_of_le hM hD))
  refine ⟨hk, ?_⟩
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkK : (k : ℝ) ≤ max (K₀ : ℝ) 1 := le_max_of_le_left (by exact_mod_cast hk.le)
  have h1 : (k : ℝ) ^ D₀ ≤ (max (K₀ : ℝ) 1) ^ (max D₀ 0) := by
    calc (k : ℝ) ^ D₀ ≤ (k : ℝ) ^ (max D₀ 0) :=
          Real.rpow_le_rpow_of_exponent_le hk1' (le_max_left _ _)
      _ ≤ _ := Real.rpow_le_rpow (by linarith) hkK (le_max_right _ _)
  have h2 : (j : ℝ) < 2 ^ j := by
    exact_mod_cast Nat.lt_two_pow_self
  have h3 : (j : ℝ) < ⌈(max (K₀ : ℝ) 1) ^ (max D₀ 0)⌉₊ + 1 :=
    lt_of_lt_of_le h2 (hD.trans (h1.trans ((Nat.le_ceil _).trans (by linarith))))
  rw [hJ₀]
  exact_mod_cast h3

end PrimeCarleson.Proof.Paper
