module

public import OAI.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
public import OAI.Combinatorics.Progressions.Estimates.SymbolFastMembership

/-!
# The dilation lemma: the symbol of a stride-`q` dilated pullback

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). In the
dilated, translated and AP-restricted niltest `T.affinePullback (fun _ _ => ℓ * q) (fun _ => ℓ * b)`
of type I (Leng's Prop 5.2, arXiv:2312.10772v5 TeX L1112-L1150) only the
orbit changes; the *symbol* of the orbit, an element of the BCH group of `ℝ ⊗ gr L`, is the image of
the symbol of `T` under the grading automorphism `δ_{ℓ q}`.

The vendored library already proves the scalar pullback version
(`OAI.Erdos3.RationalFilteredNilmanifold.Niltest.scalarAffinePullback_symbol`); the lemma here
identifies the one-variable integer affine pullback with it.

* `affinePullback_unit_orbit`: for `σ = τ = Unit` the integer affine pullback by `x ↦ c + a x`
  has the same orbit as the scalar affine pullback with `(r, shift) = (a, c)`;
* `affinePullback_unit_symbol`, `affinePullback_stride_symbol` (the dilation lemma): its symbol is
  `δ_a (T.symbol)`, respectively `δ_{ℓ q} (T.symbol)` for `a = ℓ q`, `c = ℓ b`;
* `affinePullback_unit_eval`: its values are `T.eval (c + a x)`.

Used by the type I step and by the extrapolation step.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

/-- The integer affine polynomial `c + a x` in one variable is the scalar affine polynomial with
`(r, shift) = (a, c)`. -/
theorem integerAffinePolynomial_unit (a c : ℤ) :
    integerAffinePolynomial (fun _ _ : Unit => a) (fun _ : Unit => c) =
      scalarAffinePolynomial (a : ℚ) (fun _ : Unit => (c : ℚ)) := by
  funext i
  simp [integerAffinePolynomial, scalarAffinePolynomial]

/-- The one-variable integer affine pullback `x ↦ c + a x` has the same orbit as the scalar affine
pullback with `(r, shift) = (a, c)`. -/
theorem affinePullback_unit_orbit (T : D.Niltest (fun _ : Unit => 1)) (a c : ℤ) :
    (T.affinePullback (fun _ _ => a) (fun _ => c)).orbit =
      (T.scalarAffinePullback (a : ℚ) (fun _ => (c : ℚ))).orbit := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute _ T.orbit.log = VectorPolynomial.substitute _ T.orbit.log
  rw [integerAffinePolynomial_unit]

/-- **The dilation lemma.** The symbol of the one-variable affine pullback `x ↦ c + a x` is the
image of the symbol of `T` under the grading automorphism `δ_a`. -/
theorem affinePullback_unit_symbol (T : D.Niltest (fun _ : Unit => 1))
    (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (a c : ℤ) :
    (T.affinePullback (fun _ _ => a) (fun _ => c)).symbol b ω hF =
      D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1) (a : ℚ)
        (T.symbol b ω hF) := by
  rw [← T.scalarAffinePullback_symbol b ω hF (a : ℚ) (fun _ => (c : ℚ))]
  exact RationalFilteredNilmanifold.Niltest.symbol_eq_of_orbit_eq _ _
    (affinePullback_unit_orbit T a c) b ω hF

/-- **The dilation lemma, stride-`q` form.** The dilated, translated, AP-restricted niltest
`T.affinePullback (fun _ _ => ℓ * q) (fun _ => ℓ * b)` has symbol `δ_{ℓ q} (T.symbol)`. -/
theorem affinePullback_stride_symbol (T : D.Niltest (fun _ : Unit => 1))
    (basis : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (basis '' {i | j ≤ ω i}))
    (ℓ q b : ℤ) :
    (T.affinePullback (fun _ _ => ℓ * q) (fun _ => ℓ * b)).symbol basis ω hF =
      D.filtration.realPolynomialSymbolDilationHom (fun _ : Unit => 1) ((ℓ * q : ℤ) : ℚ)
        (T.symbol basis ω hF) :=
  affinePullback_unit_symbol T basis ω hF (ℓ * q) (ℓ * b)

/-- The values of the one-variable affine pullback `x ↦ c + a x`. -/
theorem affinePullback_unit_eval (T : D.Niltest (fun _ : Unit => 1)) (a c : ℤ) (x : Unit → ℤ) :
    (T.affinePullback (fun _ _ => a) (fun _ => c)).eval x = T.eval (fun _ => c + a * x ()) := by
  rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback]
  congr 1
  funext i
  simp [integerAffineMap]

end PrimeCarleson.Proof.Fplus31
