module

public import PrimeCarleson.Proof.Oplus.SquareFunction.Estimate
public import PrimeCarleson.Proof.Common.Variation
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The variation estimate `varestpsi` at `p = 2`

[O+] L2011-L2023 (Source: [O+] `varestpsi`, L2011–L2016, restricted to `p = 2`): for a Schwartz
function `ψ` with `∫ ψ = 1`, `r > 2` and `f ∈ L²(ℝ)`, `‖V^r_{k∈ℤ}(A_k f)‖_{L²} ≤ C'_{r} ‖f‖_{L²}`,
`A_k f = ψ_k * f`.

The deduction: `V^r` is a seminorm in
the family, `A_k f = E_k f + b_k` with `b_k = A_k f - E_k f`, and for `r ≥ 2`
`V^r(b) ≤ 2 ‖b‖_{ℓ^r} ≤ 2 ‖b‖_{ℓ²}`; so
`V^r(A f) ≤ V^r(E f) + 2 (∑_k |b_k|²)^{1/2}` pointwise, and the `L²` norms are estimated by
Lépingle's inequality `lepingle_dyadic` (`p = 2`) and the square-function estimate
(`lintegral_tsum_schwartzSqOp_sq_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

open PrimeCarleson PrimeCarleson.Proof.Lepingle PrimeCarleson.Proof.Common

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- For `r ≥ 2`, the `r`-variation of a step family is at most twice the `ℓ²` norm:
`V^r(b) ≤ 2 (∑_k |b_k|²)^{1/2}`. -/
theorem rVariationOn_range_intCast_le {r : ℝ} (hr : 2 ≤ r) (b : ℤ → ℂ) :
    rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => b ⌊t⌋) ≤
      2 * (∑' k : ℤ, ‖b k‖ₑ ^ 2) ^ (1 / (2 : ℝ)) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  rw [← Set.image_univ, rVariationOn_intCast_image_eq]
  refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => iSup_le fun _ => ?_
  set T : ℝ≥0∞ := ∑' m : ℤ, ‖b m‖ₑ ^ 2 with hT
  have hside : ∀ φ : Fin J → Fin (J + 1), Function.Injective φ →
      (∑ i : Fin J, ‖b (k (φ i))‖ₑ ^ r) ^ (1 / r) ≤ T ^ (1 / (2 : ℝ)) := by
    intro φ hφ
    have h1 := sum_rpow_rpow_anti_exponent (Finset.univ : Finset (Fin J)) (r := 2) (s := r)
      (by norm_num) hr (fun i => ‖b (k (φ i))‖ₑ)
    refine h1.trans (ENNReal.rpow_le_rpow ?_ (by norm_num))
    simp only [ENNReal.rpow_two]
    have hinj : Function.Injective fun i : Fin J => k (φ i) := fun i i' h =>
      hφ (hk.injective h)
    calc ∑ i : Fin J, ‖b (k (φ i))‖ₑ ^ 2
        = ∑ m ∈ (Finset.univ : Finset (Fin J)).image (fun i => k (φ i)), ‖b m‖ₑ ^ 2 :=
          (Finset.sum_image (f := fun m => ‖b m‖ₑ ^ 2) (s := Finset.univ)
            (g := fun i => k (φ i)) (fun i _ i' _ h => hinj h)).symm
      _ ≤ T := ENNReal.sum_le_tsum _
  have hcs : Function.Injective (fun i : Fin J => i.castSucc) := Fin.castSucc_injective J
  have hs : Function.Injective (fun i : Fin J => i.succ) := Fin.succ_injective J
  calc (∑ i : Fin J, ‖b (k i.castSucc) - b (k i.succ)‖ₑ ^ r) ^ (1 / r)
      ≤ (∑ i : Fin J, (‖b (k i.castSucc)‖ₑ + ‖b (k i.succ)‖ₑ) ^ r) ^ (1 / r) := by
        refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        exact ENNReal.rpow_le_rpow enorm_sub_le hr0.le
    _ ≤ (∑ i : Fin J, ‖b (k i.castSucc)‖ₑ ^ r) ^ (1 / r) +
          (∑ i : Fin J, ‖b (k i.succ)‖ₑ ^ r) ^ (1 / r) :=
        ENNReal.Lp_add_le _ _ _ hr1
    _ ≤ T ^ (1 / (2 : ℝ)) + T ^ (1 / (2 : ℝ)) := add_le_add (hside _ hcs) (hside _ hs)
    _ = 2 * T ^ (1 / (2 : ℝ)) := (two_mul _).symm

/-- **Pointwise comparison**: `V^r(A f)(x) ≤ V^r(E f)(x) + 2 (∑_k |A_k f(x) - E_k f(x)|²)^{1/2}`
for `r ≥ 2`. -/
theorem rVariationOn_schwartzAvg_le {r : ℝ} (hr : 2 ≤ r) (ψ : 𝓢(ℝ, ℂ)) (f : ℝ → ℂ) (x : ℝ) :
    rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => schwartzAvg ψ ⌊t⌋ f x) ≤
      rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => dyadicAvg f ⌊t⌋ x) +
        2 * (∑' k : ℤ, ‖schwartzSqOp ψ k f x‖ₑ ^ 2) ^ (1 / (2 : ℝ)) := by
  have hsplit : (fun t : ℝ => schwartzAvg ψ ⌊t⌋ f x) =
      (fun t : ℝ => dyadicAvg f ⌊t⌋ x) + (fun t : ℝ => schwartzSqOp ψ ⌊t⌋ f x) := by
    funext t
    simp only [Pi.add_apply, schwartzSqOp]
    ring
  rw [hsplit]
  exact (rVariationOn_add_le (by linarith) _ _ _).trans
    (add_le_add le_rfl (rVariationOn_range_intCast_le hr (fun k => schwartzSqOp ψ k f x)))

/-- **`varestpsi` at `p = 2`**, explicit constant, measurable `f`:
`‖V^r(A_k f)‖₂ ≤ (2688 r/(r-2) + 2 C_ψ) ‖f‖₂`. -/
theorem varestpsi_two_of_measurable {ψ : 𝓢(ℝ, ℂ)} (hψ : ∫ t, ψ t = 1) {C : ℝ}
    (hC : ∀ u : ℝ, (1 + |u|) ^ 2 * ‖deriv ψ u‖ ≤ C) {r : ℝ} (hr : 2 < r) {f : ℝ → ℂ}
    (hfm : Measurable f) (hf : MemLp f 2 volume) :
    (∫⁻ x, rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => schwartzAvg ψ ⌊t⌋ f x) ^ (2 : ℝ)) ^
        (1 / (2 : ℝ)) ≤
      (ENNReal.ofReal (672 * 2 * (2 / (2 - 1)) * (r / (r - 2))) + 2 * squareFunctionConst ψ C) *
        (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  set V : ℝ → ℝ≥0∞ := fun x =>
    rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => schwartzAvg ψ ⌊t⌋ f x) with hV
  set U : ℝ → ℝ≥0∞ := fun x =>
    rVariationOn r (Set.range ((↑) : ℤ → ℝ)) (fun t => dyadicAvg f ⌊t⌋ x) with hU
  set W : ℝ → ℝ≥0∞ := fun x => (∑' k : ℤ, ‖schwartzSqOp ψ k f x‖ₑ ^ 2) ^ (1 / (2 : ℝ)) with hW
  set K : ℝ≥0∞ := squareFunctionConst ψ C with hK
  set N : ℝ≥0∞ := (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) with hN
  have hUm : Measurable U := by
    have := measurable_rVariationOn_dyadic r f Set.univ
    simpa only [Set.image_univ] using this
  have hWm : Measurable W :=
    (Measurable.tsum fun k =>
      (measurable_schwartzSqOp ψ k hfm).enorm.pow_const 2).pow_const _
  have hpt : ∀ x, V x ^ (2 : ℝ) ≤ (U x + 2 * W x) ^ (2 : ℝ) := fun x =>
    ENNReal.rpow_le_rpow (rVariationOn_schwartzAvg_le hr.le ψ f x) (by norm_num)
  -- Lépingle
  have hf' : MemLp f (ENNReal.ofReal 2) volume := by simpa using hf
  have hLep := lepingle_dyadic (p := 2) (r := r) (by norm_num) hr hf'
  -- the square function
  have hsq : ∫⁻ x, W x ^ (2 : ℝ) ≤ K ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
    have h := lintegral_tsum_schwartzSqOp_sq_le ψ hψ hC hfm hf
    simp_rw [ENNReal.rpow_two] at h ⊢
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) h
    simp only [hW]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ x, V x ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ (∫⁻ x, (U x + 2 * W x) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by norm_num)
    _ ≤ (∫⁻ x, U x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) + (∫⁻ x, (2 * W x) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_Lp_add_le hUm.aemeasurable (hWm.const_mul 2).aemeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (672 * 2 * (2 / (2 - 1)) * (r / (r - 2))) * N + 2 * (K * N) := by
        refine add_le_add hLep ?_
        have h2 : ∫⁻ x, (2 * W x) ^ (2 : ℝ) = 2 ^ (2 : ℝ) * ∫⁻ x, W x ^ (2 : ℝ) := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
          exact lintegral_const_mul' _ _ (by simp)
        rw [h2, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.rpow_mul]
        have e : (2 : ℝ≥0∞) ^ ((2 : ℝ) * (1 / 2)) = 2 := by
          rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
        rw [e]
        refine mul_le_mul_right ?_ _
        calc (∫⁻ x, W x ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
            ≤ (K ^ 2 * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
              ENNReal.rpow_le_rpow hsq (by norm_num)
          _ = K * N := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
                ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
              have e : K ^ (((2 : ℕ) : ℝ) * (1 / 2)) = K := by
                rw [show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
              rw [e]
    _ = (ENNReal.ofReal (672 * 2 * (2 / (2 - 1)) * (r / (r - 2))) + 2 * K) * N := by ring

end PrimeCarleson.Proof.Oplus
