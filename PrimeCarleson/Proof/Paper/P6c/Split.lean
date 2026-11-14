module

public import PrimeCarleson.Proof.Paper.P6c.Basic
public import PrimeCarleson.Proof.Paper.P6a.Triangle
public import PrimeCarleson.Proof.Paper.P6a.Leftover

/-!
# The pointwise decomposition of the maximal operator `C_P`

Source: main paper `s:red`, L1521–L1528 (the paper only says that the proof of `p:red-var` "carries
over"; the maximal counterparts are proved here). These are the maximal counterparts of
`triangle_split`, `main_term_split` and `low_Q_reindex` of `P6a/Triangle.lean`: the same pointwise
decompositions of the weight, with the subadditivity of `V^r` replaced by that of `supOp`. Combined
(`maximal_pointwise_chain`):

`C_P f(x) ≤ ∑_{j} sup_λ|w_{2^j} ∑_{k ≥ Q^{1/D₀}} ψ_k| + (finitely many leftover pairs)
+ ∑_k ∑_{k^{D₀} < Q ≤ M(k)} sup_λ|w_Q ψ_k| + ∑_k sup_λ|(w - w_{≤ M(k)}) ψ_k|`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The weight `w(n)/n` is `∑_{k ≥ 1} w(n) ψ_k(n)` (`∑_{k ≥ 1} ψ_k(n) = 1/n` for `|n| ≥ 1`). -/
theorem hilbW_eq_tsum (ψ : PsiData) (n : ℤ) :
    hilbW n = ∑' k : ℕ, wFun n * psiKz ψ (k + 1) n := by
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

/-- **The maximal sum over dyadic `Q`, the triangle step** (the maximal counterpart of the
triangle-inequality split of `P6a/Triangle.lean`):
`C_P f(x) ≤ sup_λ|main term| + ∑_k sup_λ|residual_k|`, with the main term `w_{≤ M(k)}` and the
residuals `w - w_{≤ M(k)}`. -/
theorem triangle_split_sup (ψ : PsiData) (f : ℤ →₀ ℂ) (x : ℤ) :
    supOp hilbW (⇑f) x ≤
      supOp (fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x +
        ∑' k : ℕ, supOp (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x := by
  obtain ⟨K, hK⟩ := exists_K_psiKz_eq_zero ψ f x
  have hv : ∀ n ∈ suppAt f x, ∀ k, K ≤ k + 1 → psiKz ψ (k + 1) n = 0 := fun n hn k hk =>
    hK (k + 1) hk n hn
  have hKk : ∀ k, K ≤ k → K ≤ k + 1 := fun k hk => by omega
  have hweight : ∀ n ∈ suppAt f x,
      hilbW n =
        (fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) n +
          (fun n => ∑ k ∈ Finset.range K, resWeight (k + 1) n * psiKz ψ (k + 1) n) n := by
    intro n hn
    have hz : ∀ k, K ≤ k → psiKz ψ (k + 1) n = 0 := fun k hk => hv n hn k (hKk k hk)
    have e1 : ∀ k, wFun n * psiKz ψ (k + 1) n =
        wLeM (k + 1) n * psiKz ψ (k + 1) n + resWeight (k + 1) n * psiKz ψ (k + 1) n := by
      intro k; simp only [resWeight]; ring
    rw [hilbW_eq_tsum ψ n]
    simp_rw [e1]
    rw [Summable.tsum_add (summable_of_ne_finset_zero (s := Finset.range K) fun k hk => by
        simp [hz k (by simpa using hk)])
      (summable_of_ne_finset_zero (s := Finset.range K) fun k hk => by
        simp [hz k (by simpa using hk)])]
    congr 1
    exact tsum_eq_sum_range_of_vanish fun k hk => by simp [hz k hk]
  calc supOp hilbW (⇑f) x
      = supOp ((fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) +
          (fun n => ∑ k ∈ Finset.range K, resWeight (k + 1) n * psiKz ψ (k + 1) n)) (⇑f) x :=
        supOp_congr_of_finsupp f x hweight
    _ ≤ _ + supOp (fun n => ∑ k ∈ Finset.range K, resWeight (k + 1) n * psiKz ψ (k + 1) n)
          (⇑f) x := supOp_add_weight_le _ _ f x
    _ ≤ _ := by
        gcongr
        exact (supOp_sum_weight_le (Finset.range K)
          (fun k n => resWeight (k + 1) n * psiKz ψ (k + 1) n) f x).trans
          (ENNReal.sum_le_tsum _)

/-- **The maximal sum over dyadic `Q`, the main-term split** (the maximal counterpart of the
main-term split of `P6a/Triangle.lean`): the main term is at most the low-denominator term, over the
pairs `(k, Q)` with `Q ≤ min(k^{D₀}, M(k))`, plus the sum over the high-denominator pairs
`k^{D₀} < Q ≤ M(k)` of the maximal operators of the single pieces. -/
theorem main_term_split_sup (ψ : PsiData) (D₀ : ℝ) (f : ℤ →₀ ℂ) (x : ℤ) :
    supOp (fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x ≤
      supOp (fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) (⇑f) x +
        ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1), supOp (pairW ψ (k + 1) j) (⇑f) x := by
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
  calc supOp (fun n => ∑' k : ℕ, wLeM (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x
      = supOp ((fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) +
          (fun n => ∑ k ∈ Finset.range K, ∑ j ∈ highJ D₀ (k + 1), pairW ψ (k + 1) j n))
          (⇑f) x := supOp_congr_of_finsupp f x hweight
    _ ≤ _ + supOp (fun n => ∑ k ∈ Finset.range K, ∑ j ∈ highJ D₀ (k + 1), pairW ψ (k + 1) j n)
          (⇑f) x := supOp_add_weight_le _ _ f x
    _ ≤ _ := by
        gcongr
        refine (supOp_sum_weight_le (Finset.range K)
          (fun k n => ∑ j ∈ highJ D₀ (k + 1), pairW ψ (k + 1) j n) f x).trans ?_
        refine le_trans (Finset.sum_le_sum fun k _ => supOp_sum_weight_le _ _ f x) ?_
        exact ENNReal.sum_le_tsum _

/-- **The maximal sum over dyadic `Q`, the reindexing** (the maximal counterpart of the reindexing
of `P6a/Triangle.lean`): the low-denominator term is at most the sum over dyadic `Q = 2^j` of
`sup_λ |∑_n f(x - n) w_Q(n) ∑_{k ≥ Q^{1/D₀}} ψ_k(n) e(λ n)|` plus the finitely many leftover pairs
`M(k) < Q ≤ k^{D₀}`. -/
theorem low_Q_reindex_sup (ψ : PsiData) {D₀ : ℝ} (hD : 0 < D₀) (f : ℤ →₀ ℂ)
    (x : ℤ) :
    supOp (fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) (⇑f) x ≤
      ∑' j : ℕ, supOp (fun n => wQ (2 ^ j) n * psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x +
        ∑ q ∈ (leftoverSet_finite D₀).toFinset, supOp (pairW ψ q.1 q.2) (⇑f) x := by
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
  have hstep : supOp (fun n => ∑' k : ℕ, ∑ j ∈ lowJ D₀ (k + 1), pairW ψ (k + 1) j n) (⇑f) x ≤
      supOp (fun n => ∑ j ∈ Finset.range J, (G j n + -H j n)) (⇑f) x :=
    (supOp_congr_of_finsupp f x hweight).le
  refine hstep.trans ?_
  refine (supOp_sum_weight_le (Finset.range J) (fun j n => G j n + -H j n) f x).trans ?_
  have hsplit : ∀ j, supOp (fun n => G j n + -H j n) (⇑f) x ≤
      supOp (G j) (⇑f) x + supOp (H j) (⇑f) x := fun j => by
    refine (supOp_add_weight_le (G j) (fun n => -H j n) f x).trans ?_
    rw [supOp_neg_weight]
  refine (Finset.sum_le_sum fun j _ => hsplit j).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ((ENNReal.sum_le_tsum _)) ?_
  -- the leftover part
  have hH : ∀ j, supOp (H j) (⇑f) x ≤ ∑ k ∈ Finset.range K,
      if (k + 1, j) ∈ leftoverSet D₀ then supOp (pairW ψ (k + 1) j) (⇑f) x else 0 := by
    intro j
    refine (supOp_sum_weight_le (Finset.range K)
      (fun k n => if (k + 1, j) ∈ leftoverSet D₀ then pairW ψ (k + 1) j n else 0) f x).trans ?_
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hl : (k + 1, j) ∈ leftoverSet D₀
    · simp [hl]
    · simp only [hl, ite_false]
      rw [show (fun n => (0 : ℂ)) = (0 : ℤ → ℂ) from rfl,
        supOp_zero_weight]
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
  calc ∑ p ∈ S, supOp (pairW ψ (φ p).1 (φ p).2) (⇑f) x
      = ∑ q ∈ S.image φ, supOp (pairW ψ q.1 q.2) (⇑f) x :=
        (Finset.sum_image (f := fun q : ℕ × ℕ => supOp (pairW ψ q.1 q.2) (⇑f) x)
          (fun a _ b _ h => hinj h)).symm
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun q hq => ?_
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
        rw [hS, Finset.mem_sigma, Finset.mem_filter] at hp
        exact (Set.Finite.mem_toFinset _).2 hp.2.2


/-- **The pointwise chain**: for `D₀ > 0`,
`C_P f ≤ ∑_j sup|w_{2^j} ∑_{k ≥ k₀(2^j)} ψ_k| + ∑_{leftover} sup|w_Q ψ_k| +
∑_k ∑_{j ∈ highJ} sup|w_{2^j} ψ_k| + ∑_k sup|(w - w_{≤ M(k)}) ψ_k|`. -/
theorem maximal_pointwise_chain (ψ : PsiData) {D₀ : ℝ} (hD : 0 < D₀) (f : ℤ →₀ ℂ) (x : ℤ) :
    supOp hilbW (⇑f) x ≤
      ((∑' j : ℕ, supOp (fun n => wQ (2 ^ j) n * psiTailZ ψ (kminD D₀ (2 ^ j)) n) (⇑f) x +
        ∑ q ∈ (leftoverSet_finite D₀).toFinset, supOp (pairW ψ q.1 q.2) (⇑f) x) +
        ∑' k : ℕ, ∑ j ∈ highJ D₀ (k + 1), supOp (pairW ψ (k + 1) j) (⇑f) x) +
        ∑' k : ℕ, supOp (fun n => resWeight (k + 1) n * psiKz ψ (k + 1) n) (⇑f) x :=
  (triangle_split_sup ψ f x).trans (add_le_add
    ((main_term_split_sup ψ D₀ f x).trans (add_le_add (low_Q_reindex_sup ψ hD f x) le_rfl))
    le_rfl)

end PrimeCarleson.Proof.Paper
