/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Estimates/QuarticSurvivorMultilinearization.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Data.Fintype.BigOperators
public import OAI.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
public import OAI.Combinatorics.Progressions.Estimates.MixedPermutationTensor
@[expose] public section

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

abbrev QuarticReplicatedIndex := ReplicatedIndex (mixedCorrelationDegree 3)

def quarticReplica (j : Fin 3) : QuarticReplicatedIndex := ⟨1, ⟨j.val, j.isLt⟩⟩

def quarticRepeatedCoordinates : List QuarticReplicatedIndex :=
  [quarticReplica 0, quarticReplica 1, quarticReplica 2]

def quarticInput (h : ℤ) (v : Fin 3 → ℤ) (j : QuarticReplicatedIndex) : ℤ :=
  if j.1 = 0 then h else if j.2.val = 0 then v 0 else if j.2.val = 1 then v 1 else v 2

namespace NativeMultidegreeNilcharacter

end NativeMultidegreeNilcharacter

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

namespace NativeMultidegreeNilcharacter

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
