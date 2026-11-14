/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialPatchProductBudget.lean
Changes: Lean module/public-import conversion; unneeded declarations and imports were removed.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
@[expose] public section

namespace OAI

section

namespace Erdos3

open MvPolynomial

def earlierSlot {d : ℕ} (i : Fin d) (j : Fin i.val) : Fin d :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

def patchVariableWeight {σ : Type*} {d : ℕ} (w : Fin d → ℕ) (i : Fin d) :
    σ ⊕ Fin i.val → ℕ := Sum.elim (fun _ => 1) (fun j => w (earlierSlot i j))

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

namespace PolynomialPatch

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open MvPolynomial

variable {X : Type*} {s d : ℕ}

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d n D E : ℕ}

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3
namespace PolynomialPatch

open MvPolynomial

variable {σ τ : Type*} {s : ℕ}

end PolynomialPatch
end Erdos3

end

end OAI
