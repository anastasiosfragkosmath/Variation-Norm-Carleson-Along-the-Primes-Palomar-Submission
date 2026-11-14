module

public import PrimeCarleson.Proof.Paper.P6a.Finite

/-!
# The triangle inequalities of the proof of `p:red-var`

Source: main paper `p:red-var`, L1245–L1273 (the triangle-inequality split), L1390–L1411 (the
main-term split: the split at `Q ≤ min(k^{D₀}, M(k))`) and L1460–L1474 (the reindexing: the
reindexing over `k ≥ Q^{1/D₀}` with the finitely many leftover pairs `M(k) < Q ≤ k^{D₀}`
subtracted).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- For finitely supported `f` and fixed `x` there is `K` with `ψ_k(n) = 0` for all `k ≥ K` and
all `n` in `suppAt f x`. -/
theorem exists_K_psiKz_eq_zero (ψ : PsiData) (f : ℤ →₀ ℂ) (x : ℤ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ n ∈ suppAt f x, psiKz ψ k n = 0 := by
  set R := (suppAt f x).sup Int.natAbs with hR
  refine ⟨4 * R + 4, fun k hk n hn => ?_⟩
  apply psiKz_eq_zero_of_le
  have h1 : n.natAbs ≤ R := Finset.le_sup (f := Int.natAbs) hn
  have h2 : (4 * R + 4 : ℕ) < 2 ^ (4 * R + 4) := Nat.lt_two_pow_self
  have h3 : (2 : ℝ) ^ (4 * R + 4) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h5 : ((4 * R + 4 : ℕ) : ℝ) < (2 : ℝ) ^ (4 * R + 4) := by exact_mod_cast h2
  have h4 : (n.natAbs : ℝ) ≤ R := by exact_mod_cast h1
  push_cast at h5
  linarith

/-- A `tsum` over `ℕ` of a sequence vanishing from `K` on is the finite sum. -/
theorem tsum_eq_sum_range_of_vanish {g : ℕ → ℂ} {K : ℕ} (h : ∀ k, K ≤ k → g k = 0) :
    ∑' k, g k = ∑ k ∈ Finset.range K, g k :=
  tsum_eq_sum fun k hk => h k (by simpa using hk)

/-- **The triangle-inequality split, the identity**: `V^r_P f(x) = V^r(∑_n f(x - n) ∑_{k ≥ 1} w(n)
ψ_k(n) e(λ n) : λ)` (`∑_{k ≥ 1} ψ_k(n) = 1/n` for `|n| ≥ 1`). -/
theorem primeVariation_eq_varOp_tsum (ψ : PsiData) (r : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) :
    primeVariation r f x = varOp r (fun n => ∑' k : ℕ, wFun n * psiKz ψ (k + 1) n) (⇑f) x := by
  rw [primeVariation_eq_varOp]
  refine varOp_congr_of_finsupp f x fun n _ => ?_
  by_cases hn : n = 0
  · simp [hilbW, hn, psiKz_zero]
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    have h2 := ψ.tsum_psiK h1
    have h3 : ∑' k : ℕ, psiKz ψ (k + 1) n = ((1 / (n : ℝ) : ℝ) : ℂ) := by
      unfold psiKz
      rw [← Complex.ofReal_tsum, h2]
    rw [tsum_mul_left, h3]
    simp [hilbW, hn, div_eq_mul_inv]

/-- **The triangle-inequality split**: the triangle inequality for `r`-variation splits `V^r_P f(x)`
into the main term (`w_{≤ M(k)}`) and the sum over `k` of the residual terms (`w - w_{≤ M(k)}`).
Source: main paper `p:red-var`, L1245–L1273. -/
theorem triangle_split (ψ : PsiData) {r : ℝ} (hr : 1 ≤ r) (f : ℤ →₀ ℂ) (x : ℤ) :
    primeVariation r f x ≤
      varOp r (fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x +
        ∑' k : ℕ, varOp r (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x := by
  obtain ⟨K, hK⟩ := exists_K_psiKz_eq_zero ψ f x
  rw [primeVariation_eq_varOp_tsum ψ r f x]
  have hv : ∀ n ∈ suppAt f x, ∀ k, K ≤ k + 1 → psiKz ψ (k + 1) n = 0 := fun n hn k hk =>
    hK (k + 1) hk n hn
  have hKk : ∀ k, K ≤ k → K ≤ k + 1 := fun k hk => by omega
  have hweight : ∀ n ∈ suppAt f x,
      ∑' k : ℕ, wFun n * psiKz ψ (k + 1) n =
        (fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) n +
          (fun n => ∑ k ∈ Finset.range K, resWeight (k + 1) n * psiKz ψ (k + 1) n) n := by
    intro n hn
    have hz : ∀ k, K ≤ k → psiKz ψ (k + 1) n = 0 := fun k hk => hv n hn k (hKk k hk)
    have e1 : ∀ k, wFun n * psiKz ψ (k + 1) n =
        wLeM (k + 1) n * psiKz ψ (k + 1) n + resWeight (k + 1) n * psiKz ψ (k + 1) n := by
      intro k; simp only [resWeight]; ring
    simp_rw [e1]
    rw [Summable.tsum_add (summable_of_ne_finset_zero (s := Finset.range K) fun k hk => by
        simp [hz k (by simpa using hk)])
      (summable_of_ne_finset_zero (s := Finset.range K) fun k hk => by
        simp [hz k (by simpa using hk)])]
    congr 1
    exact tsum_eq_sum_range_of_vanish fun k hk => by simp [hz k hk]
  calc varOp r (fun n => ∑' k : ℕ, wFun n * psiKz ψ (k + 1) n) (⇑f) x
      = varOp r ((fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) +
          (fun n => ∑ k ∈ Finset.range K, resWeight (k + 1) n * psiKz ψ (k + 1) n)) (⇑f) x :=
        varOp_congr_of_finsupp f x hweight
    _ ≤ _ + varOp r (fun n => ∑ k ∈ Finset.range K, resWeight (k + 1) n * psiKz ψ (k + 1) n)
          (⇑f) x := varOp_add_weight_le hr _ _ f x
    _ ≤ _ := by
        gcongr
        exact (varOp_sum_weight_le hr (Finset.range K)
          (fun k n => resWeight (k + 1) n * psiKz ψ (k + 1) n) f x).trans
          (ENNReal.sum_le_tsum _)

/-- **The main-term split** (Source: main paper `p:red-var`, L1390–L1411): the main term is at most
the low-denominator term, over the pairs `(k, Q)` with `Q ≤ min(k^{D₀}, M(k))`, plus the sum over
the high-denominator pairs `k^{D₀} < Q ≤ M(k)` of the `V^r` of the single pieces. -/
theorem main_term_split (ψ : PsiData) {r : ℝ} (hr : 1 ≤ r) (D₀ : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) :
    varOp r (fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x ≤
      varOp r (fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) (⇑f) x +
        ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1), varOp r (pairW ψ (k + 1) j) (⇑f) x := by
  obtain ⟨K, hK⟩ := exists_K_psiKz_eq_zero ψ f x
  have hweight : ∀ n ∈ suppAt f x,
      ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n =
        (fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) n +
          (fun n => ∑ k ∈ Finset.range K, ∑ j ∈ highJ D₀ (k + 1), pairW ψ (k + 1) j n) n := by
    intro n hn
    have hz : ∀ k, K ≤ k → psiKz ψ (k + 1) n = 0 := fun k hk => hK (k + 1) (by omega) n hn
    have hzp : ∀ k j, K ≤ k → pairW ψ (k + 1) j n = 0 := fun k j hk => by
      simp [pairW, hz k hk]
    have e1 : ∀ k, wLeM (k + 1) n * psiKz ψ (k + 1) n =
        ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n +
          ∑ j ∈ highJ D₀ (k + 1), pairW ψ (k + 1) j n := by
      intro k
      have hj : wLeM (k + 1) n = ∑ j ∈ jSet (k + 1), wQ (2 ^ j) n := wLeM_eq_sum _ _
      rw [hj, Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not (jSet (k + 1))
        (fun j => (2 : ℝ) ^ j ≤ ((k + 1 : ℕ) : ℝ) ^ D₀)]
      rfl
    simp_rw [e1]
    rw [Summable.tsum_add (summable_of_ne_finset_zero (s := Finset.range K) fun k hk => by
        simp [hzp _ _ (by simpa using hk)])
      (summable_of_ne_finset_zero (s := Finset.range K) fun k hk => by
        simp [hzp _ _ (by simpa using hk)])]
    congr 1
    exact tsum_eq_sum_range_of_vanish fun k hk => by simp [hzp _ _ hk]
  calc varOp r (fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x
      = varOp r ((fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) +
          (fun n => ∑ k ∈ Finset.range K, ∑ j ∈ highJ D₀ (k + 1), pairW ψ (k + 1) j n))
          (⇑f) x := varOp_congr_of_finsupp f x hweight
    _ ≤ _ + varOp r (fun n => ∑ k ∈ Finset.range K, ∑ j ∈ highJ D₀ (k + 1), pairW ψ (k + 1) j n)
          (⇑f) x := varOp_add_weight_le hr _ _ f x
    _ ≤ _ := by
        gcongr
        refine (varOp_sum_weight_le hr (Finset.range K)
          (fun k n => ∑ j ∈ highJ D₀ (k + 1), pairW ψ (k + 1) j n) f x).trans ?_
        refine le_trans (Finset.sum_le_sum fun k _ => varOp_sum_weight_le hr _ _ f x) ?_
        exact ENNReal.sum_le_tsum _

/-- For `D₀ > 0`: `⌈Q^{1/D₀}⌉ ≤ m` iff `Q ≤ m^{D₀}` (`Q = 2^j`). -/
theorem kminD_le_iff {D₀ : ℝ} (hD : 0 < D₀) {j m : ℕ} :
    kminD D₀ (2 ^ j) ≤ m ↔ (2 : ℝ) ^ j ≤ (m : ℝ) ^ D₀ := by
  unfold kminD
  rw [Nat.ceil_le]
  push_cast
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ j := by positivity
  constructor
  · intro h
    have := Real.rpow_le_rpow (Real.rpow_nonneg h2 _) h hD.le
    rwa [← Real.rpow_mul h2, one_div, inv_mul_cancel₀ hD.ne', Real.rpow_one] at this
  · intro h
    have := Real.rpow_le_rpow h2 h (inv_nonneg.2 hD.le)
    rwa [← Real.rpow_mul hm, mul_inv_cancel₀ hD.ne', Real.rpow_one, ← one_div] at this

/-- The pointwise identity behind the reindexing (`D₀ > 0`): `j ∈ lowJ D₀ (k+1)` iff
`⌈(2^j)^{1/D₀}⌉ ≤ k + 1` and `(k + 1, j)` is not a leftover pair; leftover pairs satisfy the
first condition. -/
theorem lowJ_iff_ge_not_left {D₀ : ℝ} (hD : 0 < D₀) (k j : ℕ) :
    (j ∈ lowJ D₀ (k + 1) ↔ kminD D₀ (2 ^ j) ≤ k + 1 ∧ (k + 1, j) ∉ leftoverSet D₀) ∧
      ((k + 1, j) ∈ leftoverSet D₀ → kminD D₀ (2 ^ j) ≤ k + 1) := by
  rw [mem_lowJ_iff, kminD_le_iff hD]
  simp only [leftoverSet, Set.mem_ofPred_eq]
  have h1 : 1 ≤ k + 1 := by omega
  refine ⟨?_, fun h => h.2.2⟩
  constructor
  · rintro ⟨hM, hP⟩
    exact ⟨hP, fun h => absurd hM (not_le.2 h.2.1)⟩
  · rintro ⟨hP, hn⟩
    refine ⟨?_, hP⟩
    by_contra hM
    exact hn ⟨h1, not_le.1 hM, hP⟩

/-- The tail sum as a finite sum over `k < K`,
`∑_{k ≥ k₀} ψ_k(n) = ∑_{k < K, k₀ ≤ k + 1} ψ_{k+1}(n)` when `ψ_k(n) = 0` for `k ≥ K`, `k₀ ≥ 1`. -/
theorem psiTailZ_eq_sum_range (ψ : PsiData) {k₀ K : ℕ} (hk₀ : 1 ≤ k₀) {n : ℤ}
    (hz : ∀ k, K ≤ k → psiKz ψ k n = 0) :
    psiTailZ ψ k₀ n = ∑ k ∈ Finset.range K, if k₀ ≤ k + 1 then psiKz ψ (k + 1) n else 0 := by
  set a : ℕ → ℂ := fun k => if k₀ ≤ k + 1 then psiKz ψ (k + 1) n else 0 with ha
  have hvan : ∀ k, K ≤ k → a k = 0 := fun k hk => by simp [ha, hz (k + 1) (by omega)]
  have hsum : Summable a :=
    summable_of_ne_finset_zero (s := Finset.range K) fun k hk => hvan k (by simpa using hk)
  have h1 := hsum.sum_add_tsum_nat_add (k₀ - 1)
  have h0 : ∑ i ∈ Finset.range (k₀ - 1), a i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i < k₀ - 1 := Finset.mem_range.1 hi
    simp [ha, show ¬ k₀ ≤ i + 1 by omega]
  have h2 : ∀ i, a (i + (k₀ - 1)) = psiKz ψ (k₀ + i) n := by
    intro i
    have e : i + (k₀ - 1) + 1 = k₀ + i := by omega
    simp [ha, e]
  rw [h0, zero_add] at h1
  unfold psiTailZ
  simp_rw [h2] at h1
  rw [h1]
  exact tsum_eq_sum_range_of_vanish hvan

/-- **The reindexing of the low-denominator term** (Source: main paper `p:red-var`, L1460–L1474):
the low-denominator term is at most the sum over dyadic `Q = 2^j` of
`V^r(∑_n f(x - n) w_Q(n) ∑_{k ≥ Q^{1/D₀}} ψ_k(n) e(λ n) : λ)` plus the finitely many leftover pairs
`M(k) < Q ≤ k^{D₀}`. -/
theorem low_Q_reindex (ψ : PsiData) {r : ℝ} (hr : 1 ≤ r) {D₀ : ℝ} (hD : 0 < D₀) (f : ℤ →₀ ℂ)
    (x : ℤ) :
    varOp r (fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) (⇑f) x ≤
      ∑' j : ℕ, varOp r (fun n => wQ (2 ^ j) n * psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x +
        ∑ q ∈ (leftoverSet_finite D₀).toFinset, varOp r (pairW ψ q.1 q.2) (⇑f) x := by
  classical
  obtain ⟨K, hK⟩ := exists_K_psiKz_eq_zero ψ f x
  set J : ℕ := ⌊cutoffM K⌋₊ + 1 with hJ
  -- the weights `G_j` and `H_j`
  let G : ℕ → ℤ → ℂ := fun j n => wQ (2 ^ j) n * psiTailZ ψ (kminD D₀ (2 ^ j)) n
  let H : ℕ → ℤ → ℂ := fun j n => ∑ k ∈ Finset.range K,
    if (k + 1, j) ∈ leftoverSet D₀ then pairW ψ (k + 1) j n else 0
  have hlowsub : ∀ k, k < K → lowJ D₀ (k + 1) ⊆ Finset.range J := by
    intro k hk j hj
    rw [mem_lowJ_iff] at hj
    have hj1 : (j : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast (Nat.lt_two_pow_self (n := j)).le
    have h2 : (j : ℝ) ≤ cutoffM K := hj1.trans (hj.1.trans (cutoffM_mono (by omega)))
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h2))
  have hweight : ∀ n ∈ suppAt f x,
      ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n =
        ∑ j ∈ Finset.range J, (G j n + -H j n) := by
    intro n hn
    have hz : ∀ k, K ≤ k → psiKz ψ k n = 0 := fun k hk => hK k hk n hn
    have e1 : ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n =
        ∑ k ∈ Finset.range K, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n :=
      tsum_eq_sum_range_of_vanish fun k hk => Finset.sum_eq_zero fun j _ => by
        simp [pairW, hz (k + 1) (by omega)]
    have e2 : ∀ k ∈ Finset.range K, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n =
        ∑ j ∈ Finset.range J, if j ∈ lowJ D₀ (k + 1) then pairW ψ (k + 1) j n else 0 := by
      intro k hk
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (hlowsub k (Finset.mem_range.1 hk))]
    rw [e1, Finset.sum_congr rfl e2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hG : G j n = ∑ k ∈ Finset.range K,
        if kminD D₀ (2 ^ j) ≤ k + 1 then pairW ψ (k + 1) j n else 0 := by
      have hk₀ : 1 ≤ kminD D₀ (2 ^ j) := by
        unfold kminD
        exact Nat.one_le_iff_ne_zero.2 (by
          rw [Ne, Nat.ceil_eq_zero, not_le]
          exact Real.rpow_pos_of_pos (by positivity) _)
      change wQ (2 ^ j) n * psiTailZ ψ (kminD D₀ (2 ^ j)) n = _
      rw [psiTailZ_eq_sum_range ψ hk₀ hz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : kminD D₀ (2 ^ j) ≤ k + 1 <;> simp [h, pairW]
    have hH : H j n = ∑ k ∈ Finset.range K,
        if (k + 1, j) ∈ leftoverSet D₀ then pairW ψ (k + 1) j n else 0 := rfl
    rw [hG, hH, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨h1, h2⟩ := lowJ_iff_ge_not_left hD k j
    by_cases hl : (k + 1, j) ∈ leftoverSet D₀
    · have hg := h2 hl
      have : j ∉ lowJ D₀ (k + 1) := fun hh => ((h1.1 hh).2 hl).elim
      simp [this, hg, hl]
    · by_cases hg : kminD D₀ (2 ^ j) ≤ k + 1
      · have : j ∈ lowJ D₀ (k + 1) := h1.2 ⟨hg, hl⟩
        simp [this, hg, hl]
      · have : j ∉ lowJ D₀ (k + 1) := fun hh => hg (h1.1 hh).1
        simp [this, hg, hl]
  -- the estimates
  have hstep : varOp r (fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) (⇑f) x ≤
      varOp r (fun n => ∑ j ∈ Finset.range J, (G j n + -H j n)) (⇑f) x :=
    (varOp_congr_of_finsupp f x hweight).le
  refine hstep.trans ?_
  refine (varOp_sum_weight_le hr (Finset.range J) (fun j n => G j n + -H j n) f x).trans ?_
  have hsplit : ∀ j, varOp r (fun n => G j n + -H j n) (⇑f) x ≤
      varOp r (G j) (⇑f) x + varOp r (H j) (⇑f) x := fun j => by
    refine (varOp_add_weight_le hr (G j) (fun n => -H j n) f x).trans ?_
    rw [varOp_neg_weight (zero_lt_one.trans_le hr)]
  refine (Finset.sum_le_sum fun j _ => hsplit j).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ((ENNReal.sum_le_tsum _)) ?_
  -- the leftover part
  have hH : ∀ j, varOp r (H j) (⇑f) x ≤ ∑ k ∈ Finset.range K,
      if (k + 1, j) ∈ leftoverSet D₀ then varOp r (pairW ψ (k + 1) j) (⇑f) x else 0 := by
    intro j
    refine (varOp_sum_weight_le hr (Finset.range K)
      (fun k n => if (k + 1, j) ∈ leftoverSet D₀ then pairW ψ (k + 1) j n else 0) f x).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hl : (k + 1, j) ∈ leftoverSet D₀
    · simp [hl]
    · simp only [hl, ite_false]
      rw [show (fun n => (0 : ℂ)) = (0 : ℤ → ℂ) from rfl,
        varOp_zero_weight (zero_lt_one.trans_le hr)]
  refine (Finset.sum_le_sum fun j _ => hH j).trans ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_sigma']
  set S := (Finset.range K).sigma
    (fun k => (Finset.range J).filter fun j => (k + 1, j) ∈ leftoverSet D₀) with hS
  set φ : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.1 + 1, p.2) with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : a = c := by omega
    subst this; subst h2; rfl
  calc ∑ p ∈ S, varOp r (pairW ψ (φ p).1 (φ p).2) (⇑f) x
      = ∑ q ∈ S.image φ, varOp r (pairW ψ q.1 q.2) (⇑f) x :=
        (Finset.sum_image (f := fun q : ℕ × ℕ => varOp r (pairW ψ q.1 q.2) (⇑f) x)
          (fun a _ b _ h => hinj h)).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun q hq => ?_
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
        rw [hS, Finset.mem_sigma, Finset.mem_filter] at hp
        exact (Set.Finite.mem_toFinset _).2 hp.2.2

end PrimeCarleson.Proof.Paper
