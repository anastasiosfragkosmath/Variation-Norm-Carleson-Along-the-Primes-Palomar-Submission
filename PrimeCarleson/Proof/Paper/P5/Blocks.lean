module

public import PrimeCarleson.Proof.Paper.P5.Kernel
public import PrimeCarleson.Proof.Goal0.Divisors
public import PrimeCarleson.Proof.Goal0.Exponents

/-!
# The block partition of the squarefree integers in `(Q/2, Q]`

Source: main paper `e:kappa`, L2083–L2086; main paper `s:per`, L2091–L2096 and L2102–L2105.

* `sqfreeSet j` is the set of squarefree integers in `(Q/2, Q]`, `Q = 2^j`;
* `BlockPartition j κ A` (`e:kappa`) is a partition of `sqfreeSet j` into pairwise disjoint
  nonempty blocks `B` with `|B| ≈ Q^κ` in the sense `Q^κ ≤ A |B|`, `|B| ≤ A Q^κ`, exactly the
  hypotheses of the `periodicBlockMax_bound`;
* `lcmQ_le_exp` (L2091–L2096): for `B ⊆ sqfreeSet j` with
  `|B| ≤ 100 Q^κ`, `𝒬_B ≤ exp(100 log Q · Q^κ)`;
* `blocks_card_le` (the number of the blocks): `#blocks ≤ 2 A Q^{1-κ}`;
* `blockWeight_eq_sum_blocks`, `TQ_eq_sum_TQB`, `CQ_le_sum_CQB` (L2102–L2105):
  `w_Q = ∑_B w_{Q,B}`, `T^Q_λ f = ∑_B T^{Q,B}_λ f` and `C^Q f(x) ≤ ∑_B C^Q_B f(x)` for finitely
  supported `f`.
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- The squarefree integers in `(Q/2, Q]` for `Q = 2^j`. -/
def sqfreeSet (j : ℕ) : Finset ℕ := (Finset.Ioc (2 ^ j / 2) (2 ^ j)).filter Squarefree

theorem mem_sqfreeSet {j q : ℕ} : q ∈ sqfreeSet j ↔ 2 ^ j / 2 < q ∧ q ≤ 2 ^ j ∧ Squarefree q := by
  simp only [sqfreeSet, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

/-- The number of squarefree integers in `(Q/2, Q]` is at most `Q/2 + 1`. -/
theorem card_sqfreeSet_le (j : ℕ) : ((sqfreeSet j).card : ℝ) ≤ (2 : ℝ) ^ j / 2 + 1 := by
  have h1 : (sqfreeSet j).card ≤ (Finset.Ioc (2 ^ j / 2) (2 ^ j)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Nat.card_Ioc] at h1
  have h2aux : ∀ n : ℕ, n - n / 2 ≤ n / 2 + 1 := fun n => by omega
  have h2 : 2 ^ j - 2 ^ j / 2 ≤ 2 ^ j / 2 + 1 := h2aux (2 ^ j)
  calc ((sqfreeSet j).card : ℝ) ≤ ((2 ^ j / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
    _ ≤ (2 : ℝ) ^ j / 2 + 1 := by
        push_cast
        have : ((2 ^ j / 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ j / 2 := by
          rw [le_div_iff₀ (by norm_num)]
          exact_mod_cast Nat.div_mul_le_self (2 ^ j) 2
        linarith

/-- **The block partition `e:kappa`.** A partition of the squarefree integers in `(Q/2, Q]`,
`Q = 2^j`, into pairwise disjoint blocks `B` with `|B| ≈ Q^κ`: `Q^κ ≤ A |B|` and `|B| ≤ A Q^κ`. -/
structure BlockPartition (j : ℕ) (κ A : ℝ) where
  /-- The blocks. -/
  blocks : Finset (Finset ℕ)
  /-- The blocks are pairwise disjoint. -/
  pairwiseDisjoint : (blocks : Set (Finset ℕ)).PairwiseDisjoint id
  /-- The blocks cover the squarefree integers in `(Q/2, Q]`. -/
  biUnion_eq : blocks.biUnion id = sqfreeSet j
  /-- `Q^κ ≤ A |B|`. -/
  card_ge : ∀ B ∈ blocks, ((2 : ℝ) ^ j) ^ κ ≤ A * B.card
  /-- `|B| ≤ A Q^κ`. -/
  card_le : ∀ B ∈ blocks, (B.card : ℝ) ≤ A * ((2 : ℝ) ^ j) ^ κ

namespace BlockPartition

variable {j : ℕ} {κ A : ℝ} (π : BlockPartition j κ A)

theorem subset_sqfreeSet {B : Finset ℕ} (hB : B ∈ π.blocks) : B ⊆ sqfreeSet j := by
  rw [← π.biUnion_eq]
  exact Finset.subset_biUnion_of_mem id hB

theorem squarefree_of_mem {B : Finset ℕ} (hB : B ∈ π.blocks) {q : ℕ} (hq : q ∈ B) :
    Squarefree q := (mem_sqfreeSet.1 (π.subset_sqfreeSet hB hq)).2.2

theorem card_biUnion_eq : ∑ B ∈ π.blocks, B.card = (sqfreeSet j).card := by
  rw [← π.biUnion_eq, Finset.card_biUnion π.pairwiseDisjoint]
  rfl

/-- **The number of the blocks**: `#{blocks} ≤ 2 A Q^{1-κ}` (for `A > 0`; `κ ≤ 1` is not needed).
Each block has at least `Q^κ / A` elements and there are at most `Q/2 + 1` squarefree integers in
`(Q/2, Q]`. -/
theorem blocks_card_le (hA : 0 < A) :
    (π.blocks.card : ℝ) ≤ 2 * A * ((2 : ℝ) ^ j) ^ (1 - κ) := by
  set Q : ℝ := (2 : ℝ) ^ j with hQ
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by norm_num)
  have hQ0 : 0 < Q := by linarith
  have hQκ : 0 < Q ^ κ := Real.rpow_pos_of_pos hQ0 _
  have hsum : (π.blocks.card : ℝ) * (Q ^ κ / A) ≤ ((sqfreeSet j).card : ℝ) := by
    rw [← π.card_biUnion_eq]
    push_cast
    calc (π.blocks.card : ℝ) * (Q ^ κ / A) = ∑ _B ∈ π.blocks, Q ^ κ / A := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ B ∈ π.blocks, (B.card : ℝ) := Finset.sum_le_sum fun B hB => by
          rw [div_le_iff₀ hA]
          linarith [π.card_ge B hB]
  have h2 := card_sqfreeSet_le j
  have hQ2 : Q / 2 + 1 ≤ 2 * Q := by linarith
  have hexp : Q ^ (1 - κ) * Q ^ κ = Q := by
    rw [← Real.rpow_add hQ0]
    simp
  have : (π.blocks.card : ℝ) * (Q ^ κ / A) ≤ 2 * Q := by linarith
  rw [mul_div_assoc', div_le_iff₀ hA] at this
  -- `card * Q^κ ≤ 2 Q A = 2 A Q^{1-κ} Q^κ`
  have h3 : (π.blocks.card : ℝ) * Q ^ κ ≤ (2 * A * Q ^ (1 - κ)) * Q ^ κ := by
    calc (π.blocks.card : ℝ) * Q ^ κ ≤ 2 * Q * A := this
      _ = (2 * A * Q ^ (1 - κ)) * Q ^ κ := by rw [mul_assoc (2 * A), hexp]; ring
  exact le_of_mul_le_mul_right h3 hQκ

end BlockPartition

/-! ### `𝒬_B`: bound (Source: main paper `s:per`, L2091–L2096) -/

/-- `𝒬_B ≤ Q^{|B|}`, for `B ⊆ (Q/2, Q]`. -/
theorem lcmQ_le_pow_card {B : Finset ℕ} {j : ℕ} (hB : B ⊆ sqfreeSet j) :
    (lcmQ B : ℝ) ≤ ((2 : ℝ) ^ j) ^ B.card := by
  have h1 : lcmQ B ∣ ∏ q ∈ B, q := Finset.lcm_dvd_prod B id
  have hpos : 0 < ∏ q ∈ B, q := Finset.prod_pos fun q hq =>
    Nat.pos_of_ne_zero (mem_sqfreeSet.1 (hB hq)).2.2.ne_zero
  have h2 : lcmQ B ≤ ∏ q ∈ B, q := Nat.le_of_dvd hpos h1
  have h3 : (∏ q ∈ B, q) ≤ (2 ^ j) ^ B.card :=
    Finset.prod_le_pow_card B id (2 ^ j) fun q hq => (mem_sqfreeSet.1 (hB hq)).2.1
  have := h2.trans h3
  exact_mod_cast this

/-- **Bound for `𝒬_B`**: `𝒬_B ≤ exp(100 log Q · Q^κ)` for a block `B ⊆ sqfreeSet j` with
`|B| ≤ 100 Q^κ`. -/
theorem lcmQ_le_exp {B : Finset ℕ} {j : ℕ} {κ : ℝ} (hB : B ⊆ sqfreeSet j)
    (hcard : (B.card : ℝ) ≤ 100 * ((2 : ℝ) ^ j) ^ κ) :
    (lcmQ B : ℝ) ≤ Real.exp (100 * ((2 : ℝ) ^ j) ^ κ * Real.log ((2 : ℝ) ^ j)) := by
  have hQ1 : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hlog : 0 ≤ Real.log ((2 : ℝ) ^ j) := Real.log_nonneg hQ1
  calc (lcmQ B : ℝ) ≤ ((2 : ℝ) ^ j) ^ B.card := lcmQ_le_pow_card hB
    _ = Real.exp (B.card * Real.log ((2 : ℝ) ^ j)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
        ring_nf
    _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hcard hlog)

/-! ### The decomposition `C^Q f ≤ ∑_B C^Q_B f` (Source: main paper `s:per`, L2102–L2105) -/

namespace BlockPartition

variable {j : ℕ} {κ A : ℝ} (π : BlockPartition j κ A)

/-- `w_Q = ∑_B w_{Q,B}` for `Q = 2^j`: the squarefree `q` are partitioned and `μ(q) = 0`
otherwise. -/
theorem blockWeight_eq_sum_blocks (n : ℤ) :
    blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j)) n = ∑ B ∈ π.blocks, blockWeight B n := by
  classical
  unfold blockWeight
  have h1 : ∑ q ∈ Finset.Ioc (2 ^ j / 2) (2 ^ j),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) * ramanujanSum q n =
      ∑ q ∈ sqfreeSet j,
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) * ramanujanSum q n := by
    symm
    unfold sqfreeSet
    refine Finset.sum_filter_of_ne fun q _ hq => ?_
    by_contra hns
    apply hq
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
  rw [h1, ← π.biUnion_eq, Finset.sum_biUnion π.pairwiseDisjoint]
  rfl

end BlockPartition

/-- The modulated sum is additive in the weight for finitely supported `f`. -/
theorem weightedModSum_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℤ → ℂ) (f : ℤ → ℂ)
    (hf : (Function.support f).Finite) (lam : ℝ) (x : ℤ) :
    weightedModSum (fun n => ∑ i ∈ s, w i n) f lam x = ∑ i ∈ s, weightedModSum (w i) f lam x := by
  have hfin : ∀ (g : ℤ → ℂ), (Function.support fun n : ℤ => f (x - n) * g n * e (lam * n)).Finite
      := by
    intro g
    refine (hf.preimage (f := fun n : ℤ => x - n) (sub_right_injective.injOn)).subset ?_
    intro n hn
    simp only [Function.mem_support, Set.mem_preimage] at hn ⊢
    intro h
    apply hn
    simp [h]
  have hsum : ∀ i ∈ s, Summable fun n : ℤ => f (x - n) * w i n * e (lam * n) := fun i _ =>
    summable_of_ne_finset_zero (s := (hfin (w i)).toFinset) fun n hn => by
      by_contra h
      exact hn ((hfin (w i)).mem_toFinset.2 h)
  unfold weightedModSum
  rw [← Summable.tsum_finsetSum hsum]
  refine tsum_congr fun n => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

namespace KQSetup

variable (S : KQSetup)

/-- `T^Q_λ f = ∑_B T^{Q,B}_λ f` for `Q = 2^j` and finitely supported `f`. -/
theorem TQ_eq_sum_TQB {j : ℕ} {κ A : ℝ} (π : BlockPartition j κ A) (f : ℤ → ℂ)
    (hf : (Function.support f).Finite) (lam : ℝ) (x : ℤ) :
    S.TQ (2 ^ j) lam f x = ∑ B ∈ π.blocks, S.TQB (2 ^ j) B lam f x := by
  unfold TQ TQB
  have h : (fun n : ℤ => wQ (2 ^ j) n * S.KQz (2 ^ j) n) =
      fun n => ∑ B ∈ π.blocks, blockWeight B n * S.KQz (2 ^ j) n := by
    funext n
    rw [← Finset.sum_mul, wQ, π.blockWeight_eq_sum_blocks]
  rw [h]
  exact weightedModSum_finset_sum π.blocks (fun B n => blockWeight B n * S.KQz (2 ^ j) n) f hf
    lam x

/-- **The block decomposition of `C^Q`**: `C^Q f(x) ≤ ∑_B C^Q_B f(x)` for `Q = 2^j` and
finitely supported `f`. -/
theorem CQ_le_sum_CQB {j : ℕ} {κ A : ℝ} (π : BlockPartition j κ A) (f : ℤ → ℂ)
    (hf : (Function.support f).Finite) (x : ℤ) :
    S.CQ (2 ^ j) f x ≤ ∑ B ∈ π.blocks, S.CQB (2 ^ j) B f x := by
  unfold CQ CQB
  refine iSup₂_le fun lam hlam => ?_
  rw [S.TQ_eq_sum_TQB π f hf lam x]
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun B _ => ?_)
  exact le_iSup₂ (f := fun lam (_ : lam ∈ Set.Ico (0 : ℝ) 1) => ‖S.TQB (2 ^ j) B lam f x‖ₑ)
    lam hlam

end KQSetup

end PrimeCarleson.Proof.Paper
