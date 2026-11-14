module

public import PrimeCarleson.Proof.Paper.P5.SquarefreeDensity
public import PrimeCarleson.Proof.Paper.P5.Support
public import PrimeCarleson.Proof.Paper.P5.Periodic
public import PrimeCarleson.Proof.Paper.P5.ErrorKQ

/-!
# Assembly of the block partition

The block partition (`e:kappa`) exists unconditionally for `A = 24` (`exists_blockPartition_24`,
from the density `Q ≤ 24 #{squarefree n ∈ (Q/2, Q]}` and `exists_blockPartition`), and its blocks
satisfy, for `A ≤ 100`, `|B| ≤ 100 Q^κ` (`card_le_hundred`) and are nonempty
(`nonempty_of_mem`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **The block partition `e:kappa`** (unconditional): for `0 ≤ κ ≤ 1` the squarefree integers in
`(Q/2, Q]`, `Q = 2^j`, are partitioned into blocks with `Q^κ ≤ 24 |B|` and `|B| ≤ 24 Q^κ`. -/
theorem exists_blockPartition_24 (j : ℕ) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    Nonempty (BlockPartition j κ 24) := by
  refine exists_blockPartition hκ0 (by norm_num) ?_
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  calc ((2 : ℝ) ^ j) ^ κ ≤ ((2 : ℝ) ^ j) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQ1 hκ1
    _ = (2 : ℝ) ^ j := Real.rpow_one _
    _ ≤ 24 * (sqfreeSet j).card := card_sqfreeSet_ge j

namespace BlockPartition

variable {j : ℕ} {κ A : ℝ} (π : BlockPartition j κ A)

/-- `|B| ≤ 100 Q^κ` for the blocks of a partition with `A ≤ 100`. -/
theorem card_le_hundred (hA : A ≤ 100) {B : Finset ℕ} (hB : B ∈ π.blocks) :
    (B.card : ℝ) ≤ 100 * ((2 : ℝ) ^ j) ^ κ :=
  (π.card_le B hB).trans (by
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ j) ^ κ := by positivity
    nlinarith)

/-- Blocks are nonempty (`Q^κ ≤ A |B|` with `Q^κ > 0`). -/
theorem nonempty_of_mem {B : Finset ℕ} (hB : B ∈ π.blocks) : B.Nonempty := by
  have h := π.card_ge B hB
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ j) ^ κ := Real.rpow_pos_of_pos (by positivity) _
  rw [← Finset.card_pos]
  by_contra h0
  have : B.card = 0 := Nat.eq_zero_of_not_pos h0
  rw [this] at h
  simp at h
  linarith

end BlockPartition

namespace KQSetup

variable (S : KQSetup)

end KQSetup

end PrimeCarleson.Proof.Paper
