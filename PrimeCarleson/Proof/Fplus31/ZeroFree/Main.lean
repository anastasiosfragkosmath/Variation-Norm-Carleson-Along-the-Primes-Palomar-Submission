module

public import PrimeCarleson.Proof.Fplus31.ZeroFree.Zeta
public import PrimeCarleson.Proof.Fplus31.PNTSW.Inputs

/-!
# The classical zero-free region (de la Vallee Poussin)

The classical zero-free region is used by the prime number theorem in progressions of `PNTSW/`.
`classicalZeroFreeRegion` proves `PNTSW.ClassicalZeroFreeRegion` with no new hypothesis: there is an
absolute `c > 0` such that every zero `s ≠ 1` of `L(s, χ)`, `χ` primitive modulo `q`, with
`re s ≥ 1 - c / log (q (|im s| + 3))` comes from a real character modulo `q ≥ 3` and is real (the
possible exceptional zero, excluded separately by `NoSiegelZero`).

The three cases are `no_zero_nonreal` (`χ² ≠ 1`), `no_zero_real` (`χ² = 1`, `χ ≠ 1`,
`im s ≠ 0`) and `no_zero_zeta` (`χ = 1`, hence `q = 1`).  Each is the de la Vallee Poussin
argument in the Landau form: the `3-4-1` (or `1 + χ`) inequality for the logarithmic derivatives at
`σ = 1 + O(b)` against the one-sided Landau bound for `-Re L'/L` that subtracts the zero.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.ZeroFree

open PNTSW

/-- **The classical zero-free region** `PNTSW.ClassicalZeroFreeRegion`. -/
theorem classicalZeroFreeRegion : PNTSW.ClassicalZeroFreeRegion := by
  obtain ⟨cN, hcN, hN⟩ := no_zero_nonreal
  obtain ⟨cR, hcR, hR⟩ := no_zero_real
  obtain ⟨cP, hcP, hP⟩ := no_zero_zeta
  refine ⟨min cN (min cR cP), lt_min hcN (lt_min hcR hcP), ?_⟩
  intro q _ χ hprim s hs1 hreg hzero
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hH1 := log_mul_abs_add_three_gt_one hq1 s.im
  have hmono : ∀ c : ℝ, min cN (min cR cP) ≤ c →
      1 - c / Real.log (q * (|s.im| + 3)) ≤ s.re := fun c hc =>
    le_trans (by
      have : min cN (min cR cP) / Real.log (q * (|s.im| + 3)) ≤
          c / Real.log (q * (|s.im| + 3)) :=
        div_le_div_of_nonneg_right hc (by linarith)
      linarith) hreg
  by_cases hχ : χ = 1
  · exfalso
    have hq : q = 1 := by
      have h := (DirichletCharacter.isPrimitive_def χ).1 hprim
      rw [hχ, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hq
    have hz : riemannZeta s = 0 := by
      rw [← DirichletCharacter.LFunction_modOne_eq (χ := χ)]
      exact hzero
    apply hP s hs1 hz
    have := hmono cP ((min_le_right _ _).trans (min_le_right _ _))
    simpa using this
  · have h3 := three_le_of_ne_one hχ
    by_cases hχ2 : χ ^ 2 = 1
    · refine ⟨h3, im_eq_zero_of_sq_eq_one hχ2, ?_⟩
      by_contra hγ
      exact hR q χ hχ hχ2 s hzero hγ (hmono cR ((min_le_right _ _).trans (min_le_left _ _)))
    · exfalso
      exact hN q χ hχ2 s hzero (hmono cN (min_le_left _ _))

end PrimeCarleson.Proof.Fplus31.ZeroFree
