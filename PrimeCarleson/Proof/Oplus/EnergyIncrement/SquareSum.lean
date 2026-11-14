module

public import PrimeCarleson.Proof.Oplus.Estimates.All

/-!
# The Cauchy-Schwarz step of `squarebyfct` ([O+] L1512-L1525)

[O+] L1512-L1525: "`(∑_j ∑_{P ∈ S_j} |⟨f, φ_P⟩|²)² =
⟨∑ ∑ ⟨f, φ_P⟩ φ_P, f⟩² ≤ ‖f‖₂² ‖∑ ∑ ⟨f, φ_P⟩ φ_P‖₂² ≤ |F| ∑ ∑ ∑ ∑ |⟨f, φ_P⟩| |⟨f, φ_{P'}⟩|
|⟨φ_P, φ_{P'}⟩|`" (Source: [O+], L1503–L1505, by the Cauchy–Schwarz inequality).

`sq_sum_norm_sq_coeff_le` is this chain for an arbitrary finite family `U` of multitiles and an
arbitrary `g ∈ L²`: `(∑_{P ∈ U} |⟨g, φ_P⟩|²)² ≤ ‖g‖₂² ∑_{P, P' ∈ U} |c_P||c_{P'}||⟨φ_P, φ_{P'}⟩|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

variable {ρ : Idx}

/-- **The Cauchy-Schwarz step of `squarebyfct`**: for a finite family `U` of multitiles and
`g ∈ L²`, with `c_P = ⟨g, φ_P⟩`,
`(∑_{P ∈ U} |c_P|²)² ≤ ‖g‖₂² ∑_{P, P' ∈ U} |c_P| |c_{P'}| |⟨φ_P, φ_{P'}⟩|`. -/
theorem sq_sum_norm_sq_coeff_le (ch : ProfileChoice) (U : Finset (Multitile ρ)) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) :
    (∑ P ∈ U, ‖P.coeff ch g‖ ^ 2) ^ 2 ≤ (∫ x, ‖g x‖ ^ 2) *
      ∑ P ∈ U, ∑ P' ∈ U, ‖P.coeff ch g‖ * ‖P'.coeff ch g‖ *
        ‖pairing (P.wavePacket ch) (P'.wavePacket ch)‖ := by
  classical
  set φ : Multitile ρ → ℝ → ℂ := fun P => P.wavePacket ch with hφdef
  have hφ : ∀ P, MemLp (φ P) 2 volume := fun P => ch.isProfile.memLp_wavePacketOf P.I P.ωu
  set a : Multitile ρ → ℂ := fun P => P.coeff ch g with ha
  set S : ℝ → ℂ := fun x => ∑ P ∈ U, a P * φ P x with hS
  set A : ℝ := ∑ P ∈ U, ‖a P‖ ^ 2 with hA
  have hSmem : MemLp S 2 volume := by
    refine memLp_finsetSum (f := fun P x => a P * φ P x) U fun P _ => ?_
    exact (hφ P).const_mul (a P)
  have hSnorm : MemLp (fun x => ‖S x‖) 2 volume := hSmem.norm
  have hgnorm : MemLp (fun x => ‖g x‖) 2 volume := hg.norm
  have hconj : ∀ P, (starRingEnd ℂ) (a P) = ∫ x, (starRingEnd ℂ) (g x) * φ P x := by
    intro P
    rw [ha]
    simp only
    unfold Multitile.coeff pairing
    rw [← integral_conj]
    congr 1; funext x
    simp [hφdef, mul_comm]
  have hint_i : ∀ P, Integrable (fun x => (starRingEnd ℂ) (g x) * φ P x) := fun P =>
    hg.star.integrable_mul (hφ P)
  have hAeq : (A : ℂ) = ∫ x, (starRingEnd ℂ) (g x) * S x := by
    rw [hA]
    push_cast
    have : ∫ x, (starRingEnd ℂ) (g x) * S x =
        ∑ P ∈ U, a P * ∫ x, (starRingEnd ℂ) (g x) * φ P x := by
      simp only [hS, Finset.mul_sum]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun P _ => ?_
        rw [← integral_const_mul]
        congr 1; funext x; ring
      · intro P _
        have := (hint_i P).const_mul (a P)
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only; ring
    rw [this]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [← hconj P, Complex.mul_conj, ← Complex.ofReal_pow, Complex.sq_norm]
  have hA_le : A ≤ ∫ x, ‖g x‖ * ‖S x‖ := by
    have h1 : A = (((A : ℝ) : ℂ)).re := by simp
    rw [h1, hAeq]
    calc (∫ x, (starRingEnd ℂ) (g x) * S x).re ≤ ‖∫ x, (starRingEnd ℂ) (g x) * S x‖ :=
          Complex.re_le_norm _
      _ ≤ ∫ x, ‖(starRingEnd ℂ) (g x) * S x‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖g x‖ * ‖S x‖ := by
          congr 1; funext x; rw [norm_mul, Complex.norm_conj]
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun P _ => by positivity
  have hint1 : Integrable (fun x => ‖g x‖ ^ 2) := hgnorm.integrable_sq
  have hint2 : Integrable (fun x => ‖S x‖ ^ 2) := hSnorm.integrable_sq
  have hint3 : Integrable (fun x => ‖g x‖ * ‖S x‖) := hgnorm.integrable_mul hSnorm
  -- the discriminant argument: `(∫ |g||S|)² ≤ ∫ |g|² ∫ |S|²`
  have hdisc : (∫ x, ‖g x‖ * ‖S x‖) ^ 2 ≤ (∫ x, ‖g x‖ ^ 2) * ∫ x, ‖S x‖ ^ 2 := by
    set B : ℝ := ∫ x, ‖g x‖ ^ 2 with hB
    set I : ℝ := ∫ x, ‖g x‖ * ‖S x‖ with hI
    set Γ₀ : ℝ := ∫ x, ‖S x‖ ^ 2 with hΓ₀
    have h := discrim_le_zero (a := B) (b := -2 * I) (c := Γ₀) (fun t => by
      have h1 : 0 ≤ ∫ x, (t * ‖g x‖ - ‖S x‖) ^ 2 := integral_nonneg fun x => sq_nonneg _
      have e1 : ∀ x : ℝ, (t * ‖g x‖ - ‖S x‖) ^ 2 =
          ((t * t) * ‖g x‖ ^ 2 - (2 * t) * (‖g x‖ * ‖S x‖)) + ‖S x‖ ^ 2 := fun x => by ring
      have hi4 : Integrable (fun x => (t * t) * ‖g x‖ ^ 2 - (2 * t) * (‖g x‖ * ‖S x‖)) :=
        (hint1.const_mul _).sub (hint3.const_mul _)
      have h2 : ∫ x, (t * ‖g x‖ - ‖S x‖) ^ 2 = t * t * B - 2 * t * I + Γ₀ := by
        simp_rw [e1]
        rw [integral_add hi4 hint2, integral_sub (hint1.const_mul _) (hint3.const_mul _),
          integral_const_mul, integral_const_mul]
      rw [h2] at h1
      linarith)
    unfold discrim at h
    nlinarith
  -- the expansion of `∫ |S|²`
  have hS2 : ∫ x, ‖S x‖ ^ 2 ≤ ∑ P ∈ U, ∑ P' ∈ U, ‖a P‖ * ‖a P'‖ *
      ‖pairing (φ P) (φ P')‖ := by
    have hexp := integral_norm_sq_sum_eq U φ a hφ
    have hnn : 0 ≤ ∫ x, ‖S x‖ ^ 2 := integral_nonneg fun x => by positivity
    have h1 : ∫ x, ‖S x‖ ^ 2 =
        ‖∑ P ∈ U, ∑ P' ∈ U, a P * (starRingEnd ℂ) (a P') * pairing (φ P) (φ P')‖ := by
      rw [← hexp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P' _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have hAI : A ^ 2 ≤ (∫ x, ‖g x‖ * ‖S x‖) ^ 2 := pow_le_pow_left₀ hA0 hA_le 2
  have hB0 : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
  calc A ^ 2 ≤ (∫ x, ‖g x‖ * ‖S x‖) ^ 2 := hAI
    _ ≤ (∫ x, ‖g x‖ ^ 2) * ∫ x, ‖S x‖ ^ 2 := hdisc
    _ ≤ (∫ x, ‖g x‖ ^ 2) * ∑ P ∈ U, ∑ P' ∈ U, ‖a P‖ * ‖a P'‖ * ‖pairing (φ P) (φ P')‖ :=
        mul_le_mul_of_nonneg_left hS2 hB0

end PrimeCarleson.Proof.Oplus
