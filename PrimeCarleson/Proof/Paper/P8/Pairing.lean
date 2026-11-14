module

public import PrimeCarleson.Proof.Common.Variation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The pairing `⟨c, w⟩` and the two `L²` estimates of the entropy lemma

`H = ℓ²(Ξ)` is `EuclideanSpace ℂ Ξ` with `Ξ` finite, and the pairing of the entropy lemma
(Source: main paper `l:entest`, L1824–L1840) is bilinear, without
conjugation: `⟨c, w⟩ = ∑_ξ c(ξ) w(ξ)` (`pairing`), with `|⟨c, w⟩| ≤ ‖c‖ ‖w‖`.

For a finite set `U`, vectors `D_u ∈ H` with `‖D_u‖ ≤ K`, `r ≥ 2` and `g : Y → H` satisfying
(H1) `∫ ‖⟨c, g⟩‖² ≤ A₀² ‖c‖²` and (H2) `∫ ‖g‖² ≤ B₀²` (written with the lower integral of `‖·‖ₑ²`),
the function `F(y) = (∑_{u ∈ U} ‖⟨D_u, g(y)⟩‖^r)^{1/r}` satisfies

* `lintegral_sq_sum_rpow_le_A` (orthogonality): `∫ F² ≤ |U| A₀² K²`;
* `lintegral_sq_sum_rpow_le_B` (Cauchy-Schwarz): `∫ F² ≤ |U|^{2/r} K² B₀²`.

These are the two level estimates of `Levels.lean` (part of the chaining proof of main paper
`l:entest`, L1824–L1860)
before `|U|` and `K` are specialised.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

variable {Ξ : Type*} [Fintype Ξ]

/-- The bilinear (non-conjugating) pairing `⟨c, w⟩ = ∑_ξ c(ξ) w(ξ)` of `H = ℓ²(Ξ)`, as in the first
hypothesis of `l:entest` (L1830–L1833), called (H1) here. -/
def pairing (c w : EuclideanSpace ℂ Ξ) : ℂ := ∑ ξ, c ξ * w ξ

/-- `c ↦ ⟨c, w⟩` as an additive map. -/
def pairingAddHom (w : EuclideanSpace ℂ Ξ) : EuclideanSpace ℂ Ξ →+ ℂ where
  toFun c := pairing c w
  map_zero' := by simp [pairing]
  map_add' c d := by simp [pairing, add_mul, Finset.sum_add_distrib]

/-- `pairingAddHom w c = ⟨c, w⟩`. -/
@[simp] theorem pairingAddHom_apply (w c : EuclideanSpace ℂ Ξ) :
    pairingAddHom w c = pairing c w := rfl

/-- Cauchy-Schwarz: `|⟨c, w⟩| ≤ ‖c‖ ‖w‖`. -/
theorem norm_pairing_le (c w : EuclideanSpace ℂ Ξ) : ‖pairing c w‖ ≤ ‖c‖ * ‖w‖ := by
  calc ‖pairing c w‖ ≤ ∑ ξ, ‖c ξ‖ * ‖w ξ‖ := by
        refine (norm_sum_le _ _).trans ?_
        simp
    _ ≤ √(∑ ξ, ‖c ξ‖ ^ 2) * √(∑ ξ, ‖w ξ‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖c‖ * ‖w‖ := by rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]

/-- `‖⟨c, w⟩‖ₑ ≤ ‖c‖ₑ ‖w‖ₑ`. -/
theorem enorm_pairing_le (c w : EuclideanSpace ℂ Ξ) : ‖pairing c w‖ₑ ≤ ‖c‖ₑ * ‖w‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_pairing_le c w)

/-- The pairing with a coordinatewise measurable `g` is measurable. -/
theorem measurable_pairing {Y : Type*} [MeasurableSpace Y] {g : Y → EuclideanSpace ℂ Ξ}
    (hg : ∀ ξ, Measurable fun y => g y ξ) (c : EuclideanSpace ℂ Ξ) :
    Measurable fun y => pairing c (g y) :=
  Finset.measurable_sum _ fun ξ _ => (hg ξ).const_mul (c ξ)

section LevelEstimates

variable {Y ι : Type*} [MeasurableSpace Y] {ν : Measure Y} {g : Y → EuclideanSpace ℂ Ξ}

/-- Pointwise comparison `ℓ^r ≤ ℓ²` for `r ≥ 2`, squared:
`(∑ x_u^r)^{2/r} ≤ ∑ x_u²` in `ℝ≥0∞`. -/
theorem sq_sum_rpow_le_sum_sq (U : Finset ι) (x : ι → ℝ≥0∞) {r : ℝ} (hr : 2 ≤ r) :
    ((∑ u ∈ U, x u ^ r) ^ (1 / r)) ^ 2 ≤ ∑ u ∈ U, x u ^ 2 := by
  have h := PrimeCarleson.Proof.Common.sum_rpow_rpow_anti_exponent U (r := 2) (s := r)
    (by norm_num) hr x
  calc ((∑ u ∈ U, x u ^ r) ^ (1 / r)) ^ 2
      ≤ ((∑ u ∈ U, x u ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left' h 2
    _ = ∑ u ∈ U, x u ^ 2 := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        have : (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 := by norm_num
        rw [this, ENNReal.rpow_one]
        simp only [ENNReal.rpow_two]

/-- **Orthogonality estimate** (`A₀` side): for `r ≥ 2`, `‖D_u‖ ≤ K` and (H1),
`∫ (∑_{u∈U} ‖⟨D_u, g⟩‖^r)^{2/r} dν ≤ |U| A₀² K²`.

Part of the chaining proof of main paper `l:entest` (orthogonality). -/
theorem lintegral_sq_sum_rpow_le_A (hg : ∀ ξ, Measurable fun y => g y ξ) (U : Finset ι)
    (D : ι → EuclideanSpace ℂ Ξ) {K A₀ : ℝ} (hD : ∀ u ∈ U, ‖D u‖ ≤ K) {r : ℝ} (hr : 2 ≤ r)
    (hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (A₀ ^ 2 * ‖w‖ ^ 2)) :
    ∫⁻ y, ((∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r) ^ (1 / r)) ^ 2 ∂ν ≤
      ENNReal.ofReal (U.card * (A₀ ^ 2 * K ^ 2)) := by
  calc ∫⁻ y, ((∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r) ^ (1 / r)) ^ 2 ∂ν
      ≤ ∫⁻ y, ∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ 2 ∂ν :=
        lintegral_mono fun y => sq_sum_rpow_le_sum_sq U _ hr
    _ = ∑ u ∈ U, ∫⁻ y, ‖pairing (D u) (g y)‖ₑ ^ 2 ∂ν :=
        lintegral_finsetSum' U fun u _ =>
          (((measurable_pairing hg (D u)).enorm).pow_const 2).aemeasurable
    _ ≤ ∑ u ∈ U, ENNReal.ofReal (A₀ ^ 2 * K ^ 2) := by
        refine Finset.sum_le_sum fun u hu => (hH1 (D u)).trans ?_
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
        exact pow_le_pow_left₀ (norm_nonneg _) (hD u hu) 2
    _ = ENNReal.ofReal (U.card * (A₀ ^ 2 * K ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- **Cauchy-Schwarz estimate** (`B₀` side): for `r ≥ 2`, `0 ≤ K`, `‖D_u‖ ≤ K` and
(H2), `∫ (∑_{u∈U} ‖⟨D_u, g⟩‖^r)^{2/r} dν ≤ |U|^{2/r} K² B₀²`.

Part of the chaining proof of main paper `l:entest` (Cauchy-Schwarz). -/
theorem lintegral_sq_sum_rpow_le_B (U : Finset ι) (D : ι → EuclideanSpace ℂ Ξ) {K B₀ : ℝ}
    (hK : 0 ≤ K) (hD : ∀ u ∈ U, ‖D u‖ ≤ K) {r : ℝ} (hr : 2 ≤ r)
    (hH2 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B₀ ^ 2)) :
    ∫⁻ y, ((∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r) ^ (1 / r)) ^ 2 ∂ν ≤
      ENNReal.ofReal ((U.card : ℝ) ^ (2 / r) * (K ^ 2 * B₀ ^ 2)) := by
  have hr0 : 0 < r := by linarith
  set κ : ℝ≥0∞ := (U.card : ℝ≥0∞) with hκ
  have hpt : ∀ y, ((∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r) ^ (1 / r)) ^ 2 ≤
      (κ ^ (1 / r)) ^ 2 * (ENNReal.ofReal K ^ 2 * ‖g y‖ₑ ^ 2) := by
    intro y
    have h1 : ∀ u ∈ U, ‖pairing (D u) (g y)‖ₑ ≤ ENNReal.ofReal K * ‖g y‖ₑ := by
      intro u hu
      refine (enorm_pairing_le _ _).trans (mul_le_mul' ?_ le_rfl)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hD u hu)
    have h2 : ∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r ≤ κ * (ENNReal.ofReal K * ‖g y‖ₑ) ^ r := by
      calc ∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r
          ≤ ∑ _u ∈ U, (ENNReal.ofReal K * ‖g y‖ₑ) ^ r :=
            Finset.sum_le_sum fun u hu => ENNReal.rpow_le_rpow (h1 u hu) hr0.le
        _ = κ * (ENNReal.ofReal K * ‖g y‖ₑ) ^ r := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r) ^ (1 / r) ≤
        κ ^ (1 / r) * (ENNReal.ofReal K * ‖g y‖ₑ) := by
      calc (∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r) ^ (1 / r)
          ≤ (κ * (ENNReal.ofReal K * ‖g y‖ₑ) ^ r) ^ (1 / r) :=
            ENNReal.rpow_le_rpow h2 (by positivity)
        _ = κ ^ (1 / r) * (ENNReal.ofReal K * ‖g y‖ₑ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
              mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
    calc ((∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r) ^ (1 / r)) ^ 2
        ≤ (κ ^ (1 / r) * (ENNReal.ofReal K * ‖g y‖ₑ)) ^ 2 := pow_le_pow_left' h3 2
      _ = (κ ^ (1 / r)) ^ 2 * (ENNReal.ofReal K ^ 2 * ‖g y‖ₑ ^ 2) := by ring
  have hκtop : (κ ^ (1 / r)) ^ 2 * ENNReal.ofReal K ^ 2 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.rpow_ne_top_of_nonneg
      (by positivity) (by simp [hκ]))) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  calc ∫⁻ y, ((∑ u ∈ U, ‖pairing (D u) (g y)‖ₑ ^ r) ^ (1 / r)) ^ 2 ∂ν
      ≤ ∫⁻ y, ((κ ^ (1 / r)) ^ 2 * ENNReal.ofReal K ^ 2) * ‖g y‖ₑ ^ 2 ∂ν :=
        lintegral_mono fun y => by
          refine (hpt y).trans (le_of_eq ?_)
          ring
    _ = ((κ ^ (1 / r)) ^ 2 * ENNReal.ofReal K ^ 2) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν :=
        lintegral_const_mul' _ _ hκtop
    _ ≤ ((κ ^ (1 / r)) ^ 2 * ENNReal.ofReal K ^ 2) * ENNReal.ofReal (B₀ ^ 2) :=
        mul_le_mul_right hH2 _
    _ = ENNReal.ofReal ((U.card : ℝ) ^ (2 / r) * (K ^ 2 * B₀ ^ 2)) := by
        have hc : κ ^ (1 / r) = ENNReal.ofReal ((U.card : ℝ) ^ (1 / r)) := by
          rw [hκ, ← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _)
            (by positivity)]
        have hc2 : ((U.card : ℝ) ^ (1 / r)) ^ 2 = (U.card : ℝ) ^ (2 / r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
          congr 1
          push_cast
          ring
        rw [hc, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hK,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hc2]
        congr 1
        ring

end LevelEstimates

end PrimeCarleson.Proof.Paper
