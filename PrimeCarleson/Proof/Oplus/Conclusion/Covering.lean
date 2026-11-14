module

public import PrimeCarleson.Proof.Oplus.Conclusion.Stages
public import PrimeCarleson.Proof.Oplus.External.All

/-!
# The exceptional sets `G_{j,k,ℓ}` ([O+] L2603-L2616)

Source: [O+] `L1except`, L2603–L2610; [O+] `L1except`, L2611–L2616. For finitely many dyadic
intervals `I_i` the covering
function `g = ∑_i 1_{2^ℓ I_i}` has `‖g‖_{L¹} = 2^ℓ ∑ |I_i|`; if its dyadic BMO norm is at most `b`
then Fefferman-Stein interpolation (`dyadic_interpolation_dilates`) gives
`‖g‖_{L^q} ≲ ‖g‖_1^{1/q} b^{1-1/q}`, and Chebyshev's inequality bounds the measure of
`{g ≥ B}` by `C^q (2^ℓ σ) b^{q-1} / B^q`, where `σ` bounds `∑ |I_i|` (for the exponent `q ∈ ℕ`,
`q ≥ 1`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

universe u

section Covering

/-- The `L¹` norm of a covering function `∑_i 1_{c I_i}` is `c ∑_i |I_i|`. -/
theorem eLpNorm_one_covering {ι : Type u} (S : Finset ι) (D : ι → Dyadic) {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun x => ∑ i ∈ S, ((D i).dilate c).indicator (fun _ => (1 : ℝ)) x) 1 volume =
      ENNReal.ofReal c * ∑ i ∈ S, ENNReal.ofReal (D i).length := by
  have h1 : ∀ x, ‖∑ i ∈ S, ((D i).dilate c).indicator (fun _ => (1 : ℝ)) x‖ₑ =
      ∑ i ∈ S, ((D i).dilate c).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    have hnn : 0 ≤ ∑ i ∈ S, ((D i).dilate c).indicator (fun _ => (1 : ℝ)) x :=
      Finset.sum_nonneg fun i _ => indicator_nonneg (fun _ _ => zero_le_one) x
    rw [← ofReal_norm, Real.norm_of_nonneg hnn, ENNReal.ofReal_sum_of_nonneg
      (fun i _ => indicator_nonneg (fun _ _ => zero_le_one) x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ (D i).dilate c <;> simp [hx]
  have hmeas : AEStronglyMeasurable
      (fun x => ∑ i ∈ S, ((D i).dilate c).indicator (fun _ => (1 : ℝ)) x) volume :=
    (Finset.measurable_sum _ fun i _ =>
      measurable_const.indicator ((D i).measurableSet_dilate c)).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hmeas]
  simp_rw [h1]
  rw [lintegral_finsetSum _ fun i _ => measurable_const.indicator ((D i).measurableSet_dilate c)]
  simp_rw [lintegral_indicator_const ((D _).measurableSet_dilate c), one_mul, Dyadic.volume_dilate]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul hc]

/-- **The measure of `{∑_i 1_{2^ℓ I_i} ≥ B}`** (L2611-L2616, with the `L^q` bound of L2603-L2610 by
Fefferman-Stein interpolation and Chebyshev's inequality): for every `q ∈ ℕ`, `q ≥ 1`, there is
`C ≥ 0` such that if `∑ |I_i| ≤ σ` and the dyadic BMO norm of `∑_i 1_{2^ℓ I_i}` is at most `b`, then
`|{∑_i 1_{2^ℓ I_i} ≥ B}| ≤ C^q 2^ℓ σ b^{q-1} / B^q`. -/
theorem exists_measure_covering_le (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} (S : Finset ι) (D : ι → Dyadic) (ℓ : ℕ) {σ b B : ℝ},
      0 ≤ σ → 0 ≤ b → 0 < B → ∑ i ∈ S, ENNReal.ofReal (D i).length ≤ ENNReal.ofReal σ →
      dyadicBMO (fun x => ∑ i ∈ S, ((D i).dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ)) x) ≤
        ENNReal.ofReal b →
      volume {x | B ≤ ∑ i ∈ S, ((D i).dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ)) x} ≤
        ENNReal.ofReal (C ^ q * (2 ^ ℓ * σ) * b ^ (q - 1) / B ^ q) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨C, hC0, hC⟩ := dyadic_interpolation_dilates.{u} hq1
  refine ⟨C, hC0, fun {ι} S D ℓ σ b B hσ hb hB hS hbmo => ?_⟩
  set g : ℝ → ℝ := fun x => ∑ i ∈ S, ((D i).dilate ((2 : ℝ) ^ ℓ)).indicator (fun _ => (1 : ℝ)) x
    with hg
  have h2ℓ : (0 : ℝ) ≤ 2 ^ ℓ := by positivity
  have hL1 : eLpNorm g 1 volume ≤ ENNReal.ofReal (2 ^ ℓ * σ) := by
    rw [hg, eLpNorm_one_covering S D h2ℓ, ENNReal.ofReal_mul h2ℓ]
    exact mul_le_mul' le_rfl hS
  have hq' : ENNReal.ofReal (q : ℝ) ≠ 0 := (ENNReal.ofReal_pos.2 hq0).ne'
  have hqt : ENNReal.ofReal (q : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal (q : ℝ)).toReal = q := ENNReal.toReal_ofReal hq0.le
  have hN := mul_meas_ge_le_pow_eLpNorm' (μ := volume) (f := g) hq' hqt (ENNReal.ofReal B)
  rw [hqr] at hN
  have hsub : {x | B ≤ g x} ⊆ {x | ENNReal.ofReal B ≤ ‖g x‖ₑ} := by
    intro x hx
    have hnn : 0 ≤ g x := Finset.sum_nonneg fun i _ => indicator_nonneg (fun _ _ => zero_le_one) x
    change ENNReal.ofReal B ≤ ‖g x‖ₑ
    rw [← ofReal_norm, Real.norm_of_nonneg hnn]
    exact ENNReal.ofReal_le_ofReal hx
  have hI := hC S D ((2 : ℝ) ^ ℓ) b hb hbmo
  -- the interpolation bound, as an `ofReal`
  have hH : eLpNorm g (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (C * (2 ^ ℓ * σ) ^ (1 / (q : ℝ)) * b ^ (1 - 1 / (q : ℝ))) := by
    refine hI.trans ?_
    have e1 : eLpNorm g 1 volume ^ (1 / (q : ℝ)) ≤ ENNReal.ofReal (2 ^ ℓ * σ) ^ (1 / (q : ℝ)) :=
      ENNReal.rpow_le_rpow hL1 (by positivity)
    have hexp : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := by
      have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hq0]; exact hq1
      linarith
    have hx : 0 ≤ 2 ^ ℓ * σ := by positivity
    have e2 : ENNReal.ofReal (C * (2 ^ ℓ * σ) ^ (1 / (q : ℝ)) * b ^ (1 - 1 / (q : ℝ))) =
        ENNReal.ofReal C * ENNReal.ofReal (2 ^ ℓ * σ) ^ (1 / (q : ℝ)) *
          ENNReal.ofReal b ^ (1 - 1 / (q : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC0,
        ← ENNReal.ofReal_rpow_of_nonneg hx (by positivity),
        ← ENNReal.ofReal_rpow_of_nonneg hb hexp]
    rw [e2]
    exact mul_le_mul' (mul_le_mul' le_rfl e1) le_rfl
  have hpow : ENNReal.ofReal (C * (2 ^ ℓ * σ) ^ (1 / (q : ℝ)) * b ^ (1 - 1 / (q : ℝ))) ^ (q : ℝ) =
      ENNReal.ofReal (C ^ q * (2 ^ ℓ * σ) * b ^ (q - 1)) := by
    have hx : 0 ≤ 2 ^ ℓ * σ := by positivity
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
    congr 1
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC0 (by positivity),
      ← Real.rpow_mul hx, ← Real.rpow_mul hb, Real.rpow_natCast C, one_div_mul_cancel hq0.ne',
      Real.rpow_one]
    have : (1 - 1 / (q : ℝ)) * q = ((q - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hq]; field_simp; simp
    rw [this, Real.rpow_natCast]
  have hBq : ENNReal.ofReal B ^ q ≠ 0 := pow_ne_zero q (ENNReal.ofReal_pos.2 hB).ne'
  have hBqt : ENNReal.ofReal B ^ q ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hN' : ENNReal.ofReal B ^ (q : ℝ) = ENNReal.ofReal B ^ q := ENNReal.rpow_natCast _ _
  rw [hN'] at hN
  calc volume {x | B ≤ g x} ≤ volume {x | ENNReal.ofReal B ≤ ‖g x‖ₑ} := measure_mono hsub
    _ ≤ eLpNorm g (ENNReal.ofReal q) volume ^ (q : ℝ) / ENNReal.ofReal B ^ q := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hBq) (Or.inl hBqt), mul_comm]
        exact hN
    _ ≤ ENNReal.ofReal (C ^ q * (2 ^ ℓ * σ) * b ^ (q - 1)) / ENNReal.ofReal B ^ q := by
        refine ENNReal.div_le_div_right ?_ _
        rw [← hpow]
        exact ENNReal.rpow_le_rpow hH hq0.le
    _ = ENNReal.ofReal (C ^ q * (2 ^ ℓ * σ) * b ^ (q - 1) / B ^ q) := by
        rw [ENNReal.ofReal_div_of_pos (pow_pos hB q), ENNReal.ofReal_pow hB.le]

end Covering

end PrimeCarleson.Proof.Oplus
