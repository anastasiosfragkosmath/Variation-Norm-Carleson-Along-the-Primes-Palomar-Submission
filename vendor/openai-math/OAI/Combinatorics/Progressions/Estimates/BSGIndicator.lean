/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/BSGIndicator.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib
@[expose] public section

namespace OAI

section

section BSGIndicatorNotation

scoped[Indicator] notation3 "𝟭_[" s ", " R "]" => Set.indicator s fun _ ↦ (1 : R)

open scoped Indicator

scoped[Indicator] notation3 "𝟭_[" s "]" => 𝟭_[s, _]

end BSGIndicatorNotation

section BSGIndicatorAlgebra

open scoped Indicator

variable {F α β M₀ N₀ : Type*}

namespace Set
open scoped _root_.Set
variable [MonoidWithZero M₀] [MonoidWithZero N₀] {s : Set α}

variable [Nontrivial M₀] {a : α}

end Set

end BSGIndicatorAlgebra

section BSGIndicatorOrder

open scoped Indicator

namespace Set
open scoped _root_.Set
variable {α M : Type*} [Zero M] [One M]

section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s : Set α}

@[simp] lemma indicator_one_nonneg : 0 ≤ s.indicator (fun _ ↦ (1 : M)) :=
  _root_.Set.indicator_nonneg (by simp)

@[simp] lemma indicator_one_apply_nonneg {a : α} :
    0 ≤ s.indicator (fun _ ↦ (1 : M)) a := indicator_one_nonneg a

end Preorder

section PartialOrder
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1 : M)] {s : Set α}

@[simp]
lemma indicator_one_pos [Nontrivial M] : 0 < s.indicator (fun _ ↦ (1 : M)) ↔ s.Nonempty := by
  classical
  simp [_root_.Set.indicator_apply, lt_iff_le_not_ge, Pi.le_def, apply_ite, ite_apply, Set.Nonempty,
    zero_lt_one.not_ge]

end PartialOrder
end Set

end BSGIndicatorOrder

section BSGIndicatorStar

open scoped ComplexConjugate Indicator

namespace Set
open scoped _root_.Set
variable {α R : Type*} [CommSemiring R] [StarRing R]

@[simp] lemma conj_indicator_one_apply (s : Set α) (a : α) : conj (𝟭_[s, R] a) = 𝟭_[s] a := by
  classical simp [_root_.Set.indicator_apply]

end Set

end BSGIndicatorStar

end

end OAI
