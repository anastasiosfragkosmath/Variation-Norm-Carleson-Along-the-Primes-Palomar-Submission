/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/FixedPartnerPower.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.CyclicShortShiftSet
public import OAI.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
public import OAI.Combinatorics.Progressions.Geometry.BoxDetectionExponents
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem exists_large_fixed_choices {G K P : Type*} [Fintype K] [Fintype P]
    (H : Finset G) (hH : H.Nonempty) (rel : G → K → P → Prop)
    (hchoice : ∀ h ∈ H, ∀ k, ∃ p, rel h k p) {R : ℝ}
    (hcount : (Fintype.card P : ℝ) ≤ Real.exp R) :
    ∃ (q : K → P) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-R * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, rel h k (q k) := by
  classical
  choose choices hchoices using hchoice
  obtain ⟨h0, hh0⟩ := hH
  have hH : H.Nonempty := ⟨h0, hh0⟩
  let code : G → (K → P) := fun h => if hh : h ∈ H then choices h hh else choices h0 hh0
  have hcode (h : G) (hh : h ∈ H) (k : K) : rel h k (code h k) := by
    simpa [code, hh] using hchoices h hh k
  have hcodeCount : (((Set.univ : Set (K → P)).ncard : ℕ) : ℝ) ≤
      Real.exp (R * Fintype.card K) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow]
    calc
      _ ≤ (Real.exp R) ^ Fintype.card K := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, S, hsub, hSn, hconst, hsize⟩ := exists_exponential_constant_fiber
    H hH code Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcodeCount
  refine ⟨q, S, hsub, hSn, ?_, ?_⟩
  · simpa only [neg_mul] using hsize
  · intro h hh k
    rw [← hconst h hh]
    exact hcode h (hsub hh) k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G]

variable [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI
