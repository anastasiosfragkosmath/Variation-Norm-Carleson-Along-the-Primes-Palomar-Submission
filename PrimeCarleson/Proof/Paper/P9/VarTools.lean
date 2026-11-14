module

public import PrimeCarleson.Proof.Paper.P8.EntropyLemma
public import PrimeCarleson.Proof.Common.VariationIntegral
public import PrimeCarleson.Proof.Common.Variation

/-!
# Tools for the variation arguments of `p:variable`

Source: main paper `p:variable`, L1898–L1929.

* `tsum_mul_le_sqrt_mul_sqrt`: Cauchy-Schwarz for `ℝ≥0∞`-valued series over `ℤ`;
* `enorm_euclid_sq`: `‖x‖ₑ² = ∑_ξ ‖x_ξ‖ₑ²` in `EuclideanSpace ℂ Ξ`;
* `rVariationOn_lt_top`: the `r`-variation over a finite index set is finite (Lemma S,
  `P8/Chain.lean`);
* `rVariationOnH_euclid_le`: the chain-wise Minkowski step of `p:variable` (L1925–L1929): for
  `s ≥ 2`,
  `V^s(c_t : t ∈ T) ≤ (∑_ξ V^s(c_t(ξ) : t ∈ T)²)^{1/2}` for `ℓ²(Ξ)`-valued `c`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- **Cauchy-Schwarz for series over `ℤ`** in `ℝ≥0∞`. -/
theorem tsum_mul_le_sqrt_mul_sqrt (f g : ℤ → ℝ≥0∞) :
    ∑' y : ℤ, f y * g y ≤
      (∑' y : ℤ, f y ^ 2) ^ (1 / 2 : ℝ) * (∑' y : ℤ, g y ^ 2) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ)
    Real.HolderConjugate.two_two (f := f) (g := g) measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable
  simp only [lintegral_count, Pi.mul_apply, ENNReal.rpow_two] at h
  exact h

/-- `(X^{1/2})² = X` in `ℝ≥0∞`. -/
theorem enorm_rpow_half_sq (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `(X²)^{1/2} = X` in `ℝ≥0∞`. -/
theorem enorm_sq_rpow_half (X : ℝ≥0∞) : (X ^ 2) ^ (1 / 2 : ℝ) = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **Minkowski for series over `ℤ`** in `ℝ≥0∞`, `p = 2`. -/
theorem tsum_sq_add_le (f g : ℤ → ℝ≥0∞) :
    (∑' x : ℤ, (f x + g x) ^ 2) ^ (1 / 2 : ℝ) ≤
      (∑' x : ℤ, f x ^ 2) ^ (1 / 2 : ℝ) + (∑' x : ℤ, g x ^ 2) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_Lp_add_le (μ := (Measure.count : Measure ℤ)) (p := 2)
    (f := f) (g := g) measurable_from_top.aemeasurable measurable_from_top.aemeasurable
    (by norm_num)
  simpa only [lintegral_count, Pi.add_apply, ENNReal.rpow_two] using h

/-- The change of variables `x ↦ x' + y` in a double series over `ℤ × ℤ`. -/
theorem tsum_tsum_shift (F : ℤ → ℤ → ℝ≥0∞) :
    ∑' x : ℤ, ∑' y : ℤ, F x y = ∑' x' : ℤ, ∑' y : ℤ, F (x' + y) y := by
  rw [ENNReal.tsum_comm, ENNReal.tsum_comm (f := fun x' y => F (x' + y) y)]
  refine tsum_congr fun y => ?_
  exact ((Equiv.addRight y).tsum_eq (fun x => F x y)).symm

/-- `ofReal (A² ∑_ξ ‖w_ξ‖²) = ofReal(A)² ∑_ξ ‖w_ξ‖ₑ²`. -/
theorem ofReal_sq_mul_sum_norm_sq {Ξ : Type*} [Fintype Ξ] {A : ℝ} (hA : 0 ≤ A) (w : Ξ → ℂ) :
    ENNReal.ofReal (A ^ 2 * ∑ ξ, ‖w ξ‖ ^ 2) = ENNReal.ofReal A ^ 2 * ∑ ξ, ‖w ξ‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hA,
    ENNReal.ofReal_sum_of_nonneg (fun ξ _ => by positivity)]
  congr 1
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The `r`-variation only depends on the values of the family on the index set. -/
theorem rVariationOn_congr {r : ℝ} {S : Set ℝ} {c c' : ℝ → ℂ} (h : ∀ t ∈ S, c t = c' t) :
    rVariationOn r S c = rVariationOn r S c' := by
  rw [← rVariationOnH_complex, ← rVariationOnH_complex]
  exact rVariationOnH_congr h

variable {Ξ : Type*} [Fintype Ξ]

/-- `‖x‖ₑ² = ∑_ξ ‖x_ξ‖ₑ²` in `ℓ²(Ξ)`. -/
theorem enorm_euclid_sq (x : EuclideanSpace ℂ Ξ) : ‖x‖ₑ ^ 2 = ∑ ξ, ‖x ξ‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun ξ _ => by positivity)]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The `r`-variation over a finite index set is finite, `1 ≤ r`. -/
theorem rVariationOn_lt_top {T : Set ℝ} (hT : T.Finite) {r : ℝ} (hr : 1 ≤ r) (a : ℝ → ℂ) :
    rVariationOn r T a < ⊤ := by
  have hr0 : 0 < r := by linarith
  have hS : (↑hT.toFinset : Set ℝ) = T := hT.coe_toFinset
  rw [← hS]
  refine lt_of_le_of_lt (rVariationOn_le_two_mul_sum hT.toFinset a hr) ?_
  refine ENNReal.mul_lt_top (by simp) (ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_)
  exact (ENNReal.sum_lt_top.2 fun u _ => ENNReal.rpow_lt_top_of_nonneg hr0.le enorm_ne_top).ne

/-- **Chain-wise Minkowski in the vector index** (Source: main paper `p:variable`, L1925–L1929):
`V^s(c_t : t ∈ T) ≤ (∑_ξ V^s(c_t(ξ) : t ∈ T)²)^{1/2}`, by the triangle inequality in `ℓ^{s/2}`. -/
theorem rVariationOnH_euclid_le {T : Set ℝ} {s : ℝ} (hs : 2 ≤ s)
    (c : ℝ → EuclideanSpace ℂ Ξ) :
    rVariationOnH s T c ≤ (∑ ξ, rVariationOn s T (fun t => c t ξ) ^ 2) ^ (1 / 2 : ℝ) := by
  refine rVariationOnH_le_iff.2 fun J t ht hS => ?_
  have hs0 : 0 < s := by linarith
  have hp : 1 ≤ s / 2 := by linarith
  set f : Ξ → Fin J → ℝ≥0∞ := fun ξ i => ‖c (t i.castSucc) ξ - c (t i.succ) ξ‖ₑ ^ 2 with hf
  have h1 := Lp_sum_le_sum (Finset.univ : Finset (Fin J)) (Finset.univ : Finset Ξ) f hp
  have e1 : ∀ i : Fin J, ∑ ξ, f ξ i = ‖c (t i.castSucc) - c (t i.succ)‖ₑ ^ 2 := by
    intro i
    rw [enorm_euclid_sq]
    rfl
  have e2 : ∀ (ξ : Ξ) (i : Fin J),
      f ξ i ^ (s / 2) = ‖c (t i.castSucc) ξ - c (t i.succ) ξ‖ₑ ^ s := by
    intro ξ i
    simp only [hf]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have e3 : ∀ i : Fin J, (‖c (t i.castSucc) - c (t i.succ)‖ₑ ^ 2) ^ (s / 2) =
      ‖c (t i.castSucc) - c (t i.succ)‖ₑ ^ s := by
    intro i
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  simp_rw [e1, e2, e3] at h1
  -- `X := (∑_i ‖Δ_i‖ₑ^s)^{1/s}` satisfies `X² ≤ ∑_ξ (V_ξ)²`
  set X : ℝ≥0∞ := (∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ₑ ^ s) ^ (1 / s) with hX
  have hX2 : X ^ 2 = (∑ i : Fin J, ‖c (t i.castSucc) - c (t i.succ)‖ₑ ^ s) ^ (1 / (s / 2)) := by
    rw [hX, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    field_simp
  have hV : ∀ ξ : Ξ, (∑ i : Fin J, ‖c (t i.castSucc) ξ - c (t i.succ) ξ‖ₑ ^ s) ^ (1 / (s / 2)) ≤
      rVariationOn s T (fun u => c u ξ) ^ 2 := by
    intro ξ
    have hle : (∑ i : Fin J, ‖c (t i.castSucc) ξ - c (t i.succ) ξ‖ₑ ^ s) ^ (1 / s) ≤
        rVariationOn s T (fun u => c u ξ) :=
      le_rVariationOnH (r := s) (S := T) (c := fun u => c u ξ) ht hS
    calc (∑ i : Fin J, ‖c (t i.castSucc) ξ - c (t i.succ) ξ‖ₑ ^ s) ^ (1 / (s / 2))
        = ((∑ i : Fin J, ‖c (t i.castSucc) ξ - c (t i.succ) ξ‖ₑ ^ s) ^ (1 / s)) ^ 2 := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          congr 1
          push_cast
          field_simp
      _ ≤ rVariationOn s T (fun u => c u ξ) ^ 2 := by gcongr
  have h2 : X ^ 2 ≤ ∑ ξ, rVariationOn s T (fun t => c t ξ) ^ 2 := by
    rw [hX2]
    refine h1.trans (Finset.sum_le_sum fun ξ _ => hV ξ)
  calc X = (X ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow h2 (by norm_num)

end PrimeCarleson.Proof.Paper
