/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FilteredLieTree.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
@[expose] public section

namespace OAI

section

namespace Erdos3

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

inductive FilteredLieTree (F : NilpotentLieFiltration L s) : ℕ → ℕ → Type u where
  | leaf {d : ℕ} (hd : 0 < d) (x : L) (hx : x ∈ F.layer d) : FilteredLieTree F d 1
  | bracket {d e r t : ℕ} (a : FilteredLieTree F d r) (b : FilteredLieTree F e t) :
      FilteredLieTree F (d + e) (r + t)

namespace FilteredLieTree

variable {F : NilpotentLieFiltration L s}

def eval : {d r : ℕ} → FilteredLieTree F d r → L
  | _, _, .leaf _ x _ => x
  | _, _, .bracket a b => ⁅eval a, eval b⁆

@[simp] theorem eval_leaf {d : ℕ} (hd : 0 < d) (x : L) (hx : x ∈ F.layer d) :
    eval (leaf hd x hx) = x := rfl

@[simp] theorem eval_bracket {d e r t : ℕ} (a : FilteredLieTree F d r)
    (b : FilteredLieTree F e t) : eval (bracket a b) = ⁅eval a, eval b⁆ := rfl

theorem rank_le_degree {d r : ℕ} (a : FilteredLieTree F d r) : r ≤ d := by
  induction a with
  | leaf hd x hx => omega
  | bracket a b ha hb => omega

theorem eval_mem {d r : ℕ} (a : FilteredLieTree F d r) : a.eval ∈ F.layer d := by
  induction a with
  | leaf hd x hx => exact hx
  | bracket a b ha hb => exact F.lie_mem ha hb

end FilteredLieTree

end Erdos3

end

end OAI
