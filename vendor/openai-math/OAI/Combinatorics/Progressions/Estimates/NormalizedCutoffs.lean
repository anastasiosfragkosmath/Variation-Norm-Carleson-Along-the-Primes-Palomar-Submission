/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/NormalizedCutoffs.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.MetricSpace.Lipschitz
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem abs_div_sub_div_bound {a b u v r D M E : ℝ} (hr : 0 < r)
    (hu : r ≤ u) (hv : r ≤ v) (hD : 0 ≤ D) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hab : |a - b| ≤ D) (hb : |b| ≤ M) (huv : |u - v| ≤ E) :
    |a / u - b / v| ≤ D / r + M * E / (r * r) := by
  have hu0 : 0 < u := hr.trans_le hu
  have hv0 : 0 < v := hr.trans_le hv
  have heq : a / u - b / v = (a - b) / u + b * (v - u) / (u * v) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(a - b) / u| + |b * (v - u) / (u * v)| := abs_add_le _ _
    _ = |a - b| / u + |b| * |u - v| / (u * v) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hu0, abs_of_pos (mul_pos hu0 hv0), abs_sub_comm v u]
    _ ≤ D / r + M * E / (r * r) :=
      add_le_add (div_le_div₀ hD hab hr hu)
        (div_le_div₀ (mul_nonneg hM hE) (mul_le_mul hb huv (abs_nonneg _) hM)
          (mul_pos hr hr) (mul_le_mul hu hv hr.le hu0.le))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal Manifold ContDiff

variable {ι X : Type*} [Fintype ι]

end Erdos3

end

end OAI
