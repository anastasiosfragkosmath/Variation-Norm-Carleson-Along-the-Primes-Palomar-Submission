module

public import PrimeCarleson.Proof.Lepingle.Path.Domination
public import PrimeCarleson.Proof.Lepingle.Path.GeometricSum

/-!
# The variation is bounded by the square functions along the stopping times

Source: Zorin-Kranich's notes, (02-Lepingle.tex, L140–L152), pathwise, together with the constant
bookkeeping of the geometric series that follows it (L164-L165).

For a path `f : ℕ → E` and a horizon `N`, the square sum along the level-`m` stopping times is
`sqFun f N m = (∑_{j < N} dist (f (τ^{(m)}_j ∧ N)) (f (τ^{(m)}_{j+1} ∧ N))^2)^{1/2}`: the square
function `S_{(m)}` of the sampled sequence `j ↦ f (τ^{(m)}_j ∧ N)` (all further increments vanish).

* `seqVariationOn_sq_le` : `V^r(f; 0..N)^2 ≤ 64 ∑_{m ≥ 2} 2^{-(m-2)(r-2)} S_{(m)}^2`
  (display (2.7) with `ρ = 2`, i.e. the middle term of L145-L147, squared);
* `seqVariationOn_le_tsum_sqFun`:
  `V^r(f; 0..N) ≤ 8 ∑_{m ≥ 2} 2^{-(m-2)(r-2)/2} S_{(m)}` for every `r > 2` (sum over `k = m - 2`
  with the weights `lepingleWeight r k`);
* `tsum_ofReal_lepingleWeight_le`: `∑_m 2^{-(m-2)(r-2)/2} ≤ (3/2) r/(r-2)` in `ℝ≥0∞`.

All constants are absolute and uniform in `r > 2`, `f` and `N`.
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {E : Type*} [PseudoMetricSpace E]

/-- The square function `S_{(m)}` of the path sampled along the level-`m` stopping times on the
horizon `[0, N]`: `(∑_{j < N} dist (f (τ_j ∧ N)) (f (τ_{j+1} ∧ N))^2)^{1/2}` in `ℝ≥0∞`
(Zorin-Kranich's notes, L140-L144; the increments with `j ≥ N` vanish). -/
def sqFun (f : ℕ → E) (N m : ℕ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range N, sampleIncrement f N m j ^ 2) ^ (1 / 2 : ℝ)

/-- `S_{(m)}^2 = ∑_{j < N} (increment_j)^2`. -/
theorem sqFun_sq (f : ℕ → E) (N m : ℕ) :
    sqFun f N m ^ 2 = ∑ j ∈ Finset.range N, sampleIncrement f N m j ^ 2 := by
  unfold sqFun
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `ofReal` of the weight of (2.7) at `ρ = 2` is the square of the `ofReal` of the weight. -/
private theorem ofReal_rpow_weight {r : ℝ} (hr : 2 < r) (k : ℕ) :
    ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) ^ (r - 2) = ENNReal.ofReal (lepingleWeight r k) ^ 2 := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
    ← ENNReal.ofReal_pow (lepingleWeight_nonneg r k), lepingleWeight_sq]

/-- `∑ xₖ² ≤ (∑ xₖ)²` for nonnegative terms (`ℓ² ≤ ℓ¹`), the second inequality of L145-L152. -/
theorem tsum_sq_le_sq_tsum (x : ℕ → ℝ≥0∞) : ∑' k, x k ^ 2 ≤ (∑' k, x k) ^ 2 := by
  calc ∑' k, x k ^ 2 = ∑' k, x k * x k := by simp [sq]
    _ ≤ ∑' k, x k * ∑' k, x k := ENNReal.tsum_le_tsum fun k => by
        gcongr
        exact ENNReal.le_tsum k
    _ = (∑' k, x k) * ∑' k, x k := ENNReal.tsum_mul_right
    _ = (∑' k, x k) ^ 2 := (sq _).symm

/-- The squared form of display (2.7) at `ρ = 2` in terms of the square functions:
`V^r(f; 0..N)^2 ≤ 64 ∑_{m ≥ 2} 2^{-(m-2)(r-2)} S_{(m)}^2` (the sum over `k = m - 2`). -/
theorem seqVariationOn_sq_le {r : ℝ} (hr : 2 < r) (f : ℕ → E) (N : ℕ) :
    seqVariationOn r f N ^ 2 ≤
      64 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) ^ 2 * sqFun f N (k + 2) ^ 2 := by
  have h := seqVariationOn_rpow_le_tsum (ρ := 2) two_pos hr f N
  simp only [tsum_sampleIncrement_rpow two_pos f N] at h
  simp only [ENNReal.rpow_two, ofReal_rpow_weight hr, ← sqFun_sq] at h
  calc seqVariationOn r f N ^ 2
      ≤ 8 ^ 2 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) ^ 2 * sqFun f N (k + 2) ^ 2 := h
    _ = 64 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) ^ 2 * sqFun f N (k + 2) ^ 2 := by
        norm_num

/-- Squares compare as their roots in `ℝ≥0∞`: `V^2 ≤ c^2` implies `V ≤ c`. -/
private theorem le_of_sq_le_sq {V c : ℝ≥0∞} (h : V ^ 2 ≤ c ^ 2) : V ≤ c := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_two] at h
  exact (ENNReal.rpow_le_rpow_iff two_pos).1 h

/-- **The variation is bounded by the square functions** (Zorin-Kranich's notes, L145-L152):
for every `r > 2`, every path `f` and every horizon `N`,
`V^r(f; 0..N) ≤ 8 ∑_{m ≥ 2} 2^{-(m-2)(r-2)/2} S_{(m)}` (sum over `k = m - 2`). -/
theorem seqVariationOn_le_tsum_sqFun {r : ℝ} (hr : 2 < r) (f : ℕ → E) (N : ℕ) :
    seqVariationOn r f N ≤
      8 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) * sqFun f N (k + 2) := by
  refine le_of_sq_le_sq ?_
  calc seqVariationOn r f N ^ 2
      ≤ 64 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) ^ 2 * sqFun f N (k + 2) ^ 2 :=
        seqVariationOn_sq_le hr f N
    _ = 64 * ∑' k : ℕ, (ENNReal.ofReal (lepingleWeight r k) * sqFun f N (k + 2)) ^ 2 := by
        simp only [mul_pow]
    _ ≤ 64 * (∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) * sqFun f N (k + 2)) ^ 2 :=
        mul_le_mul_right (tsum_sq_le_sq_tsum _) _
    _ = (8 * ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) * sqFun f N (k + 2)) ^ 2 := by
        rw [mul_pow]
        norm_num

/-- The geometric series of Zorin-Kranich's notes (L164-L165) in `ℝ≥0∞`:
`∑_{m ≥ 2} 2^{-(m-2)(r-2)/2} ≤ (3/2) r/(r-2)` for `r > 2`. -/
theorem tsum_ofReal_lepingleWeight_le {r : ℝ} (hr : 2 < r) :
    ∑' k : ℕ, ENNReal.ofReal (lepingleWeight r k) ≤ ENNReal.ofReal (3 / 2 * (r / (r - 2))) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (lepingleWeight_nonneg r) (summable_lepingleWeight hr)]
  exact ENNReal.ofReal_le_ofReal (tsum_lepingleWeight_le hr)

end PrimeCarleson.Proof.Lepingle
