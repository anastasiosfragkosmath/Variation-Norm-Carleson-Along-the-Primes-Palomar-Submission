module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The two analytic inputs on the classical zero-free region

The prime number theorem in progressions on the classical zero-free region (`PNTSW/Main.lean`) takes
two named hypotheses, both statements about Mathlib's `DirichletCharacter.LFunction`:

* `NoSiegelZero`: the Landau-Siegel real-zero gap, exactly the statement of
  `OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap` of the vendored `openai/math`
  library (commit 4eaee87): there is an absolute `c > 0` with `c ≤ (1 - β) log q` for every real
  zero `β ∈ (0,1)` of the `L`-function of a real primitive character modulo `q ≥ 3`;
* `ClassicalZeroFreeRegion`: the de la Vallée Poussin zero-free region for primitive characters:
  every zero `s` of `L(s, χ)` with `re s ≥ 1 - c / log (q (|im s| + 3))` belongs to a real
  character modulo `q ≥ 3` and is real (this is the possible exceptional zero; for `q = 1`, that is
  for `ζ`, there is no such zero).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

/-- **Absence of Siegel zeros** (the Landau-Siegel real-zero gap): there is an absolute `c > 0` such
that every real zero `β ∈ (0, 1)` of the `L`-function of a real primitive nonprincipal character
modulo `q ≥ 3` satisfies `c ≤ (1 - β) log q`. This is the statement of the vendored library's
`OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap`. -/
def NoSiegelZero : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ)

/-- **The classical zero-free region** (de la Vallée Poussin), for primitive characters: there is
an absolute `c > 0` such that if `χ` is a primitive character modulo `q` and `s ≠ 1` satisfies
`1 - c / log (q (|im s| + 3)) ≤ re s` and `L(s, χ) = 0`, then `q ≥ 3`, `χ` is real, and `s` is
real (the exceptional zero, excluded by `NoSiegelZero`).  For `q = 1` (the Riemann zeta function)
the region is zero-free. -/
def ClassicalZeroFreeRegion : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (q * (|s.im| + 3)) ≤ s.re → χ.LFunction s = 0 →
        3 ≤ q ∧ (∀ a : ZMod q, (χ a).im = 0) ∧ s.im = 0

end PrimeCarleson.Proof.Fplus31.PNTSW
