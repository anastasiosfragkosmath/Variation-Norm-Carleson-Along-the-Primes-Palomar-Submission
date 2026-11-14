module

public import PrimeCarleson.Proof.Paper.P8.Pairing
public import PrimeCarleson.Proof.Paper.P8.Increments

/-!
# The level estimates of the entropy lemma

Part of the chaining proof of main paper `l:entest` (L1824–L1860), with explicit constants.

For `v ≥ 1` put `F_v(y) = (∑_{u ∈ U_v} ‖⟨D_v(u), g(y)⟩‖^r)^{1/r}` (`levelNorm`). Under (V) with
`λ > 0`, `2 < s`, `2 ≤ r`, (H1) and (H2):

  `‖F_v‖_{L²(ν)} ≤ 3 √(3/2) λ min {A₀ 2^{v(s/2-1)}, B₀ 2^{-v(1-s/r)}}`

(`levelNorm_l2_le`). The `A₀` bound is `levelNorm_l2_le_A` (orthogonality, `ℓ^r ≤ ℓ²`, `|U_v| <
(3/2) 2^{vs}` and `‖D_v‖ ≤ 3λ2^{-v}`), the `B₀` bound is `levelNorm_l2_le_B` (Cauchy-Schwarz and
`(3/2)^{2/r} ≤ 3/2`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

variable {Ξ : Type*} [Fintype Ξ]

/-- `F_v(w) = (∑_{u ∈ U_v} ‖⟨D_v(u), w⟩‖^r)^{1/r}`, the `ℓ^r` norm on the step set `U_v` of the
pairings of the level increments with `w = g(y)`. -/
def levelNorm (c : ℕ → EuclideanSpace ℂ Ξ) (lam : ℝ) (N v : ℕ) (r : ℝ)
    (w : EuclideanSpace ℂ Ξ) : ℝ≥0∞ :=
  (∑ u ∈ levelStops c lam N v, ‖pairing (levelIncrement c lam v u) w‖ₑ ^ r) ^ (1 / r)

/-- `ofReal (Z²)` bounds `X` implies `X^{1/2} ≤ ofReal Z`. -/
theorem rpow_half_le_ofReal {X : ℝ≥0∞} {Z : ℝ} (hZ : 0 ≤ Z)
    (h : X ≤ ENNReal.ofReal (Z ^ 2)) : X ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Z := by
  calc X ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (Z ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal ((Z ^ 2) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg Z) (by norm_num)
    _ = ENNReal.ofReal Z := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hZ]

section

variable {c : ℕ → EuclideanSpace ℂ Ξ} {N : ℕ} {s lam : ℝ}
  {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {g : Y → EuclideanSpace ℂ Ξ}

/-- `(2^{v(s/2-1)})² = 2^{vs} / (2^v)²`. -/
theorem two_rpow_sq_eq (v : ℕ) (s : ℝ) :
    ((2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1))) ^ 2 = (2 : ℝ) ^ ((v : ℝ) * s) / ((2 : ℝ) ^ v) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), eq_div_iff (by positivity),
    ← Real.rpow_natCast ((2 : ℝ) ^ v) 2, ← Real.rpow_natCast (2 : ℝ) v,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

/-- **Level estimate, `A₀` side** (orthogonality): for `v ≥ 1`, `2 < s`, `2 ≤ r`, (V) with `λ > 0`
and (H1), `‖F_v‖_{L²} ≤ 3 √(3/2) λ A₀ 2^{v(s/2-1)}`.

Part of the chaining proof of main paper `l:entest` (L1824–L1860). -/
theorem levelNorm_l2_le_A (hg : ∀ ξ, Measurable fun y => g y ξ)
    (hV : ChainBound c N s lam) (hs : 2 < s) (hlam : 0 < lam) (hN : 0 < N) {v : ℕ} (hv : 1 ≤ v)
    {r : ℝ} (hr : 2 ≤ r) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (A₀ ^ 2 * ‖w‖ ^ 2)) :
    (∫⁻ y, levelNorm c lam N v r (g y) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (3 * √(3 / 2) * lam * A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1))) := by
  have hZ : 0 ≤ 3 * √(3 / 2) * lam * A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1)) := by positivity
  refine rpow_half_le_ofReal hZ ?_
  have hD : ∀ u ∈ levelStops c lam N v, ‖levelIncrement c lam v u‖ ≤ 3 * (lam / 2 ^ v) :=
    fun u _ => norm_levelIncrement_le hlam.le hv u
  refine (lintegral_sq_sum_rpow_le_A hg _ (levelIncrement c lam v) hD hr hH1).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard := card_levelStops_lt hV hs hlam hN hv
  have h2v : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
  have hsq := two_rpow_sq_eq v s
  have h32 : (√(3 / 2) : ℝ) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hrhs : (3 * √(3 / 2) * lam * A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1))) ^ 2 =
      (3 / 2 * (2 : ℝ) ^ ((v : ℝ) * s)) * (A₀ ^ 2 * (3 * (lam / 2 ^ v)) ^ 2) := by
    calc (3 * √(3 / 2) * lam * A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1))) ^ 2
        = 9 * (√(3 / 2)) ^ 2 * lam ^ 2 * A₀ ^ 2 *
            ((2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1))) ^ 2 := by ring
      _ = (3 / 2 * (2 : ℝ) ^ ((v : ℝ) * s)) * (A₀ ^ 2 * (3 * (lam / 2 ^ v)) ^ 2) := by
          rw [h32, hsq]
          field_simp
          ring
  rw [hrhs]
  exact mul_le_mul_of_nonneg_right hcard.le (by positivity)

/-- **Level estimate, `B₀` side** (Cauchy-Schwarz): for `v ≥ 1`, `2 < s`, `s < r`, (V) with `λ > 0`
and (H2), `‖F_v‖_{L²} ≤ 3 √(3/2) λ B₀ 2^{-v(1-s/r)}`.

Part of the chaining proof of main paper `l:entest` (L1824–L1860). -/
theorem levelNorm_l2_le_B (hV : ChainBound c N s lam) (hs : 2 < s) (hlam : 0 < lam)
    (hN : 0 < N) {v : ℕ} (hv : 1 ≤ v) {r : ℝ} (hsr : s < r) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hH2 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B₀ ^ 2)) :
    (∫⁻ y, levelNorm c lam N v r (g y) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (3 * √(3 / 2) * lam * B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r)))) := by
  have hr2 : 2 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hZ : 0 ≤ 3 * √(3 / 2) * lam * B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r))) := by positivity
  refine rpow_half_le_ofReal hZ ?_
  have hD : ∀ u ∈ levelStops c lam N v, ‖levelIncrement c lam v u‖ ≤ 3 * (lam / 2 ^ v) :=
    fun u _ => norm_levelIncrement_le hlam.le hv u
  have hK : 0 ≤ 3 * (lam / 2 ^ v) := by positivity
  refine (lintegral_sq_sum_rpow_le_B _ (levelIncrement c lam v) hK hD hr2 hH2).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard := card_levelStops_lt hV hs hlam hN hv
  have h32 : (√(3 / 2) : ℝ) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have h2r : 2 / r ≤ 1 := by rw [div_le_one hr0]; exact hr2
  -- `|U|^{2/r} ≤ (3/2) 2^{2vs/r}`
  have hpow : (((levelStops c lam N v).card : ℝ)) ^ (2 / r) ≤
      3 / 2 * (2 : ℝ) ^ (2 * ((v : ℝ) * s) / r) := by
    calc (((levelStops c lam N v).card : ℝ)) ^ (2 / r)
        ≤ (3 / 2 * (2 : ℝ) ^ ((v : ℝ) * s)) ^ (2 / r) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hcard.le (by positivity)
      _ = (3 / 2 : ℝ) ^ (2 / r) * ((2 : ℝ) ^ ((v : ℝ) * s)) ^ (2 / r) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ (3 / 2 : ℝ) ^ (1 : ℝ) * ((2 : ℝ) ^ ((v : ℝ) * s)) ^ (2 / r) := by
          gcongr
          · norm_num
      _ = 3 / 2 * (2 : ℝ) ^ (2 * ((v : ℝ) * s) / r) := by
          rw [Real.rpow_one, ← Real.rpow_mul (by norm_num)]
          congr 2
          ring
  have hexp : ((2 : ℝ) ^ (-((v : ℝ) * (1 - s / r)))) ^ 2 =
      (2 : ℝ) ^ (2 * ((v : ℝ) * s) / r) / ((2 : ℝ) ^ v) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), eq_div_iff (by positivity),
      ← Real.rpow_natCast ((2 : ℝ) ^ v) 2, ← Real.rpow_natCast (2 : ℝ) v,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    field_simp
    ring
  have hrhs : (3 * √(3 / 2) * lam * B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r)))) ^ 2 =
      (3 / 2 * (2 : ℝ) ^ (2 * ((v : ℝ) * s) / r)) * ((3 * (lam / 2 ^ v)) ^ 2 * B₀ ^ 2) := by
    calc (3 * √(3 / 2) * lam * B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r)))) ^ 2
        = 9 * (√(3 / 2)) ^ 2 * lam ^ 2 * B₀ ^ 2 *
            ((2 : ℝ) ^ (-((v : ℝ) * (1 - s / r)))) ^ 2 := by ring
      _ = (3 / 2 * (2 : ℝ) ^ (2 * ((v : ℝ) * s) / r)) * ((3 * (lam / 2 ^ v)) ^ 2 * B₀ ^ 2) := by
          rw [h32, hexp]
          field_simp
          ring
  rw [hrhs]
  exact mul_le_mul_of_nonneg_right hpow (by positivity)

/-- **Level estimates**: for `v ≥ 1`, `2 < s < r`, (V) with `λ > 0`, (H1) and (H2),
`‖F_v‖_{L²(ν)} ≤ 3 √(3/2) λ min {A₀ 2^{v(s/2-1)}, B₀ 2^{-v(1-s/r)}}`.

Part of the chaining proof of main paper `l:entest` (L1824–L1860). -/
theorem levelNorm_l2_le (hg : ∀ ξ, Measurable fun y => g y ξ)
    (hV : ChainBound c N s lam) (hs : 2 < s) (hlam : 0 < lam) (hN : 0 < N) {v : ℕ} (hv : 1 ≤ v)
    {r : ℝ} (hsr : s < r) {A₀ B₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hH1 : ∀ w : EuclideanSpace ℂ Ξ,
      ∫⁻ y, ‖pairing w (g y)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (A₀ ^ 2 * ‖w‖ ^ 2))
    (hH2 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B₀ ^ 2)) :
    (∫⁻ y, levelNorm c lam N v r (g y) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (3 * √(3 / 2) * lam * min (A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1)))
        (B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r))))) := by
  have hA := levelNorm_l2_le_A hg hV hs hlam hN hv (by linarith : 2 ≤ r) hA₀ hH1
  have hB := levelNorm_l2_le_B hV hs hlam hN hv hsr hB₀ hH2
  have hc : 0 ≤ 3 * √(3 / 2) * lam := by positivity
  rw [mul_min_of_nonneg _ _ hc]
  rcases le_total (3 * √(3 / 2) * lam * (A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1))))
      (3 * √(3 / 2) * lam * (B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r))))) with h | h
  · rw [min_eq_left h, show 3 * √(3 / 2) * lam * (A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1))) =
      3 * √(3 / 2) * lam * A₀ * (2 : ℝ) ^ ((v : ℝ) * (s / 2 - 1)) by ring]
    exact hA
  · rw [min_eq_right h, show 3 * √(3 / 2) * lam * (B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r)))) =
      3 * √(3 / 2) * lam * B₀ * (2 : ℝ) ^ (-((v : ℝ) * (1 - s / r))) by ring]
    exact hB

end

end PrimeCarleson.Proof.Paper
