/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/CovolumeFactorBounds.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Tactic
@[expose] public section

namespace OAI

section

namespace Erdos3

theorem covolume_index_graph_bounds {a I E C d : ℝ}
    (hd : 0 < d) (ha : 1 / d ≤ a) (hI : 1 ≤ I) (hE : 1 ≤ E)
    (hprod : a * I * E ≤ C) : a ≤ C ∧ I ≤ C * d ∧ E ≤ C * d := by
  have ha0 : 0 ≤ a := (one_div_pos.mpr hd).le.trans ha
  have hI0 : 0 ≤ I := zero_le_one.trans hI
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have haI : a * I ≤ C :=
    (le_mul_of_one_le_right (mul_nonneg ha0 hI0) hE).trans hprod
  have haE : a * E ≤ C := by
    calc
      a * E ≤ (a * I) * E := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right ha0 hI) hE0
      _ ≤ C := hprod
  refine ⟨(le_mul_of_one_le_right ha0 hI).trans haI, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mp
    calc
      I / d = (1 / d) * I := by ring
      _ ≤ a * I := mul_le_mul_of_nonneg_right ha hI0
      _ ≤ C := haI
  · apply (div_le_iff₀ hd).mp
    calc
      E / d = (1 / d) * E := by ring
      _ ≤ a * E := mul_le_mul_of_nonneg_right ha hE0
      _ ≤ C := haE

end Erdos3

end

end OAI
