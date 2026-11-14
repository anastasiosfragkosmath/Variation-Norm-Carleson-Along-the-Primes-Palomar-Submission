/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NativeFixedFactoredQuadruples.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Estimates.NativeSelectedCorrelators
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedMixed (h : W.shifts) (x : ZMod N) : ℂ :=
  W.mixed.evalCyclic N (W.selectedWitness h).coordinate.1 (correlationInput h.val x)

noncomputable def selectedRank (h : W.shifts) (x : ZMod N) : ℂ :=
  W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x

noncomputable def selectedLower (h : W.shifts) (x : ZMod N) : ℂ :=
  (W.selectedWitness h).test.evalCyclic N (fun _ => x)

theorem selectedProduct_eq (h : W.shifts) (x : ZMod N) :
    W.selectedProduct h x = W.selectedMixed h x * W.selectedRank h x * W.selectedLower h x := rfl

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

end Erdos3.NativeCorrelationStructure

end

end OAI
