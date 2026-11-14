/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/ProgressionPartitionComposition.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
@[expose] public section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure FiniteProgressionPartition (N : ℕ) where
  Label : Type
  labelFintype : Fintype Label
  start : Label → ℕ
  step : Label → ℕ
  length : Label → ℕ
  step_pos : ∀ i, 0 < step i
  equiv : (Σ i : Label, Fin (length i)) ≃ Fin N
  equiv_val : ∀ i (j : Fin (length i)), (equiv ⟨i, j⟩).val = start i + step i * j.val

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3.FiniteProgressionPartition

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3.FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

end Erdos3.FiniteProgressionPartition

end

end OAI
