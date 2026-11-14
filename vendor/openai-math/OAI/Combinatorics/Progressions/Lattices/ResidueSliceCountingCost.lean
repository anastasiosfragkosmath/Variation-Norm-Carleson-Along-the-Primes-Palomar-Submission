/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Lattices/ResidueSliceCountingCost.lean
Changes: Lean module/public-import conversion; unneeded declarations were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Tactic
@[expose] public section

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

noncomputable def residueIndexLower (a r v : ℤ) : ℤ :=
  ⌈((a : ℚ) - (v : ℚ)) / (r : ℚ)⌉

noncomputable def residueIndexLength (a b r v : ℤ) : ℕ :=
  (residueIndexLower b r v - residueIndexLower a r v).toNat

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI
