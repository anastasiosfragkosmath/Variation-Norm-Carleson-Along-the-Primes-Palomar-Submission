/-
Modified for this repository: ported to Lean modules.
Derived from openai/math at 4eaee87548250b2682affda7d05d947c05554bae.
Upstream file: lean/OAI/NumberTheory/SiegelZeros/EntireFunctions/EntireLogarithm.lean
Changes: Lean module/public-import conversion only.
Original notices are retained. License: Apache-2.0; see vendor/openai-math/LICENSE.
-/
module
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
@[expose] public section

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W03

theorem exists_entire_logarithm (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  have hlog : Differentiable ℂ (logDeriv f) := by
    intro z
    exact ((hf.analyticAt z).deriv.differentiableAt).div (hf z) (hne z)
  obtain ⟨g, hg⟩ := hlog.isExactOn_univ
  have hg' : ∀ z, HasDerivAt g (logDeriv f z) z := fun z => hg z (Set.mem_univ z)
  have hgd : Differentiable ℂ g := fun z => (hg' z).differentiableAt
  have he : Differentiable ℂ (fun z => Complex.exp (g z)) := hgd.cexp
  have heq : Set.EqOn (logDeriv f) (logDeriv (fun z => Complex.exp (g z))) Set.univ := by
    intro z _
    have hd := (hg' z).cexp
    rw [logDeriv_apply (fun z => Complex.exp (g z)), hd.deriv]
    simp [Complex.exp_ne_zero]
  obtain ⟨c, hc, hfc⟩ :=
    (logDeriv_eqOn_iff hf.differentiableOn he.differentiableOn
      isOpen_univ isPreconnected_univ (fun z _ => Complex.exp_ne_zero (g z))
      (fun z _ => hne z)).mp heq
  refine ⟨fun z => Complex.log c + g z, hgd.const_add _, ?_⟩
  intro z
  rw [Complex.exp_add, Complex.exp_log hc]
  simpa only [Pi.smul_apply, smul_eq_mul] using hfc (Set.mem_univ z)

end SiegelZerosAwei.W03

end

end SiegelZeros

end OAI
