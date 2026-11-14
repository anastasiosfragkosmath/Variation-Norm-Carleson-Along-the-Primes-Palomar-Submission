module

public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dyadic blocks below a level `D`

Part of the Vaughan decomposition in the proof of [F+] Proposition 3.1: the dyadic decomposition
behind Leng23 Proposition `p:type1type2correlation` (arXiv:2312.10772v5 TeX
L1096-L1110). The statements of the type I and type II steps (`C2/TypeI.lean`,
`C2/TypeIIBoxes.lean`) use the blocks `(L/2, L]` with `L³ ≤ N²`. To keep `L ≤ D` with `D³ ≤ N²` the
blocks are cut from the top: the index `blockIndex D d = ⌊log₂ ⌊D/d⌋⌋` puts `d ∈ [1, D]` in
`(L/2, L]` with `L = ⌊D/2^i⌋`.

* `dyadicBlock L = {ℓ : L/2 < ℓ ≤ L}` (`mem_dyadicBlock`, `card_dyadicBlock_le`);
* `blockSet D i`, `blockTop D i = ⌊D/2^i⌋`, `blockSet_subset_dyadic`;
* `exists_block_sum_ge`: pigeonhole over the `⌊log₂ D⌋ + 1` blocks for nonnegative reals;
* `exists_block_pair_norm_ge`: pigeonhole over pairs of blocks for a double sum of complex numbers.
-/

@[expose] public noncomputable section

open Finset

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The dyadic block `{ℓ ∈ ℕ : L/2 < ℓ ≤ L}`. -/
def dyadicBlock (L : ℕ) : Finset ℕ := Ioc (L / 2) L

/-- Membership in the dyadic block, in real form `L/2 < ℓ ≤ L`. -/
theorem mem_dyadicBlock {L ℓ : ℕ} :
    ℓ ∈ dyadicBlock L ↔ (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L := by
  unfold dyadicBlock
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by exact_mod_cast h2⟩
    have : L < 2 * ℓ := by omega
    have : (L : ℝ) < 2 * ℓ := by exact_mod_cast this
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by exact_mod_cast h2⟩
    have : (L : ℝ) < 2 * ℓ := by linarith
    have : L < 2 * ℓ := by exact_mod_cast this
    omega

/-- The dyadic block `(L/2, L]` has at most `L` elements. -/
theorem card_dyadicBlock_le (L : ℕ) : (dyadicBlock L).card ≤ L := by
  unfold dyadicBlock
  rw [Nat.card_Ioc]
  omega

/-- The index of the dyadic block of `d ∈ [1, D]`: `⌊log₂ ⌊D/d⌋⌋`. -/
def blockIndex (D d : ℕ) : ℕ := Nat.log 2 (D / d)

/-- The top `⌊D / 2^i⌋` of the `i`-th block. -/
def blockTop (D i : ℕ) : ℕ := D / 2 ^ i

/-- The `i`-th block of `[1, D]`. -/
def blockSet (D i : ℕ) : Finset ℕ := (Icc 1 D).filter fun d => blockIndex D d = i

/-- The top `⌊D/2^i⌋` of a block is at most `D`. -/
theorem blockTop_le (D i : ℕ) : blockTop D i ≤ D := Nat.div_le_self _ _

/-- The `i`-th block is contained in `[1, D]`. -/
theorem blockSet_subset (D i : ℕ) : blockSet D i ⊆ Icc 1 D := Finset.filter_subset _ _

/-- The block index is below `⌊log₂ D⌋ + 1`. -/
theorem blockIndex_lt {D d : ℕ} : blockIndex D d < Nat.log 2 D + 1 := by
  unfold blockIndex
  exact Nat.lt_succ_of_le (Nat.log_mono_right (Nat.div_le_self _ _))

/-- The `i`-th block of `[1, D]` lies in the dyadic block `(L/2, L]`, `L = ⌊D/2^i⌋`. -/
theorem blockSet_subset_dyadic (D i : ℕ) : blockSet D i ⊆ dyadicBlock (blockTop D i) := by
  intro d hd
  simp only [blockSet, Finset.mem_filter, Finset.mem_Icc] at hd
  obtain ⟨⟨hd1, hdD⟩, hi⟩ := hd
  have hDd : D / d ≠ 0 := (Nat.div_pos hdD (by omega)).ne'
  have h1 : 2 ^ i ≤ D / d := by
    rw [← hi]
    exact Nat.pow_log_le_self 2 hDd
  have h2 : D / d < 2 ^ (i + 1) := by
    rw [← hi]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  rw [dyadicBlock, blockTop, Finset.mem_Ioc]
  constructor
  · rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.div_lt_iff_lt_mul (by positivity)]
    have := (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mp h2
    rw [mul_comm] at this
    exact this
  · rw [Nat.le_div_iff_mul_le (by positivity)]
    have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp h1
    rw [mul_comm] at this
    exact this

/-- Pigeonhole over the blocks of `[1, D]` for nonnegative terms. -/
theorem exists_block_sum_ge (D : ℕ) (g : ℕ → ℝ) {ξ : ℝ} (h : ξ ≤ ∑ d ∈ Icc 1 D, g d) :
    ∃ i < Nat.log 2 D + 1, ξ / (Nat.log 2 D + 1 : ℕ) ≤ ∑ d ∈ blockSet D i, g d := by
  have hfib : ∑ i ∈ range (Nat.log 2 D + 1), ∑ d ∈ blockSet D i, g d = ∑ d ∈ Icc 1 D, g d := by
    refine Finset.sum_fiberwise_of_maps_to (g := blockIndex D) (fun d hd => ?_) g
    exact Finset.mem_range.mpr blockIndex_lt
  have hne : (range (Nat.log 2 D + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨i, hi, hle⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => ξ / (Nat.log 2 D + 1 : ℕ)) (g := fun i => ∑ d ∈ blockSet D i, g d) (by
      rw [hfib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have : (0 : ℝ) < (Nat.log 2 D + 1 : ℕ) := by positivity
      rw [mul_div_cancel₀ _ this.ne']
      exact h)
  exact ⟨i, Finset.mem_range.mp hi, hle⟩

/-- Pigeonhole over pairs of blocks of `[1, D]` for a double sum of complex numbers. -/
theorem exists_block_pair_norm_ge (D : ℕ) (z : ℕ → ℕ → ℂ) {ξ : ℝ}
    (h : ξ ≤ ‖∑ c ∈ Icc 1 D, ∑ w ∈ Icc 1 D, z c w‖) :
    ∃ i < Nat.log 2 D + 1, ∃ j < Nat.log 2 D + 1,
      ξ / ((Nat.log 2 D + 1 : ℕ) : ℝ) ^ 2 ≤ ‖∑ c ∈ blockSet D i, ∑ w ∈ blockSet D j, z c w‖ := by
  set J := Nat.log 2 D + 1 with hJ
  have hmaps : ∀ d ∈ Icc 1 D, blockIndex D d ∈ range J := fun d hd =>
    Finset.mem_range.mpr blockIndex_lt
  have hfib : ∀ F : ℕ → ℂ, ∑ c ∈ Icc 1 D, F c =
      ∑ i ∈ range J, ∑ c ∈ blockSet D i, F c := fun F =>
    (Finset.sum_fiberwise_of_maps_to (g := blockIndex D) hmaps F).symm
  have hsplit : ∑ c ∈ Icc 1 D, ∑ w ∈ Icc 1 D, z c w =
      ∑ i ∈ range J, ∑ j ∈ range J, ∑ c ∈ blockSet D i, ∑ w ∈ blockSet D j, z c w := by
    rw [hfib (fun c => ∑ w ∈ Icc 1 D, z c w)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [hfib (fun w => z _ w)]
    rw [Finset.sum_comm]
  have htri : ‖∑ c ∈ Icc 1 D, ∑ w ∈ Icc 1 D, z c w‖ ≤
      ∑ i ∈ range J, ∑ j ∈ range J, ‖∑ c ∈ blockSet D i, ∑ w ∈ blockSet D j, z c w‖ := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact norm_sum_le _ _
  have hne : (range J).Nonempty := ⟨0, by simp [hJ]⟩
  have hJpos : (0 : ℝ) < J := by positivity
  obtain ⟨i, hi, hle⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => ξ / (J : ℝ))
    (g := fun i => ∑ j ∈ range J, ‖∑ c ∈ blockSet D i, ∑ w ∈ blockSet D j, z c w‖) (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hJpos.ne']
      exact h.trans htri)
  obtain ⟨j, hj, hle'⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => ξ / (J : ℝ) / (J : ℝ))
    (g := fun j => ‖∑ c ∈ blockSet D i, ∑ w ∈ blockSet D j, z c w‖) (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hJpos.ne']
      exact hle)
  refine ⟨i, Finset.mem_range.mp hi, j, Finset.mem_range.mp hj, ?_⟩
  have hsq : ξ / (J : ℝ) ^ 2 = ξ / (J : ℝ) / (J : ℝ) := by rw [sq, div_div]
  rw [hsq]
  exact hle'

end PrimeCarleson.Proof.Fplus31
