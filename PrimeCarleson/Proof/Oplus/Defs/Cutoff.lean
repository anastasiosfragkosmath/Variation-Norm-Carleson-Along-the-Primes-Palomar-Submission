module

public import PrimeCarleson.Proof.Oplus.Defs.Dyadic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The cutoff `ν` and the partition functions `φ_{J,i}` of [O+]

[O+] L942-L958: "Let `ν` be a `C^∞` function from `ℝ` to
`[0,1]` which vanishes on `(-∞, -10^{-2}]`, is identically equal to `1` on `[10^{-2}, ∞)`, and so
that `ν'(x) ≥ 0` for `-10^{-2} < x < 10^{-2}`. Given an interval `J = [a,b)`, and
`i ∈ {-1,0,1}`, define `φ_{J,i}(ξ) = ν((ξ - a)/(2^i (b-a))) - ν((ξ - b)/(b-a))`. Thus if `c(J)`
is the center of `J`, then `φ_{J,i}(ξ) = ν_i((ξ - c(J))/|J|)` where
`ν_i(η) = ν(2^{-i}(η + 1/2)) - ν(η - 1/2)`, and we notice for `i ∈ {-1,0,1}` both `ν_i` and
`√ν_i` are `C^∞` functions supported in `[-13/25, 13/25]` (more precisely in
`[-13/25, 51/100]`)."`

Source: [O+], L942–L946 (`phiJi`, `nuFamily`) and the supporting claim of L948–L958. The paper
asserts the smoothness of `√ν_i` without argument; it does *not* follow from the listed
properties of an arbitrary `ν`.

## The choice of `ν`

* `nu` is an explicit function with the properties printed in [O+] (L942-L943),
  `ν(x) = smoothTransition (50 x + 1/2)` (Mathlib's `Real.smoothTransition`, which is `0` on
  `(-∞, 0]` and `1` on `[1, ∞)`): `nu_of_le`, `nu_of_ge`, `nu_nonneg`, `nu_le_one`, `monotone_nu`,
  `contDiff_nu`. It is *chosen* because it has the two extra properties used below and needed for
  the wave packets ([O+] L955-L958): the symmetry `ν(-x) = 1 - ν(x)` and the smoothness of `√ν`
  (`contDiff_sqrt_nu`, `√(g(x)) = g(2x)` for the exponential glue `g` and `g + g(1-·) > 0`), which
  give `√ν_i ∈ C^∞` for `i ≤ 1` (`contDiff_sqrt_nuFamily`).
* `IsProfile χ` packages what the wave-packet estimates use about the frequency profile
  `χ = ν_i` (or the reflected `ν_i(-·)` of L1119-L1121): nonnegative, `√χ` is `C^∞`, and `χ`
  vanishes outside `[-13/25, 13/25]`. It holds for `nuFamily i` and `nuFamily i (-·)` with
  `i ∈ {-1, 0, 1}` (`isProfile_nuFamily`, `isProfile_nuFamily_neg`).
-/

@[expose] public noncomputable section

open Set Filter Topology
open scoped ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### The printed properties of `ν` and the explicit choice -/

/-- The explicit cutoff `ν(x) = smoothTransition (50 x + 1/2)`: a smooth transition from `0` at
`x = -1/100` to `1` at `x = 1/100`. This is the choice of `ν` made for the formalization
(see the module docstring); it has all the properties printed in [O+] (`nu_of_le`, `nu_of_ge`,
`nu_nonneg`, `nu_le_one`, `monotone_nu`, `contDiff_nu`). -/
def nu (x : ℝ) : ℝ := Real.smoothTransition (50 * x + 1 / 2)

/-- `ν = 0` on `(-∞, -1/100]`. -/
theorem nu_of_le {x : ℝ} (hx : x ≤ -1 / 100) : nu x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- `ν = 1` on `[1/100, ∞)`. -/
theorem nu_of_ge {x : ℝ} (hx : 1 / 100 ≤ x) : nu x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- `ν ≥ 0`. -/
theorem nu_nonneg (x : ℝ) : 0 ≤ nu x := Real.smoothTransition.nonneg _

/-- `ν ≤ 1`. -/
theorem nu_le_one (x : ℝ) : nu x ≤ 1 := Real.smoothTransition.le_one _

/-- `ν` is monotone. -/
theorem monotone_nu : Monotone nu := fun _ _ h =>
  Real.smoothTransition.monotone (by linarith)

/-- `ν` is `C^∞`. -/
theorem contDiff_nu : ContDiff ℝ ∞ nu :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id |>.add contDiff_const)

/-- `smoothTransition (1 - y) = 1 - smoothTransition y`. -/
theorem smoothTransition_one_sub (y : ℝ) :
    Real.smoothTransition (1 - y) = 1 - Real.smoothTransition y := by
  have hD := Real.smoothTransition.pos_denom y
  unfold Real.smoothTransition
  rw [show 1 - (1 - y) = y by ring, add_comm (expNegInvGlue (1 - y)) (expNegInvGlue y)]
  field_simp
  ring

/-- The symmetry `ν(-x) = 1 - ν(x)` of the explicit cutoff. -/
theorem nu_neg (x : ℝ) : nu (-x) = 1 - nu x := by
  unfold nu
  rw [show 50 * -x + 1 / 2 = 1 - (50 * x + 1 / 2) by ring, smoothTransition_one_sub]

/-- `√ν` is `C^∞`: `√(smoothTransition) = g(2x) / √(g(x) + g(1-x))` with `g` the exponential glue
function. -/
theorem contDiff_sqrt_smoothTransition :
    ContDiff ℝ ∞ (fun x => √(Real.smoothTransition x)) := by
  have hD : ∀ x, 0 < expNegInvGlue x + expNegInvGlue (1 - x) := Real.smoothTransition.pos_denom
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => expNegInvGlue (2 * x)) :=
    expNegInvGlue.contDiff.comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiff ℝ ∞ (fun x : ℝ => √(expNegInvGlue x + expNegInvGlue (1 - x))) := by
    refine ContDiff.sqrt ?_ (fun x => (hD x).ne')
    exact expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))
  have key : (fun x => √(Real.smoothTransition x)) =
      fun x => expNegInvGlue (2 * x) / √(expNegInvGlue x + expNegInvGlue (1 - x)) := by
    funext x
    unfold Real.smoothTransition
    rw [Real.sqrt_div (expNegInvGlue.nonneg x)]
    congr 1
    by_cases hx : x ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hx, expNegInvGlue.zero_of_nonpos (by linarith)]
      simp
    · unfold expNegInvGlue
      have hx2 : ¬ (2 * x ≤ 0) := fun h => hx (by linarith)
      simp only [hx, hx2, ite_false]
      rw [← Real.exp_half]
      congr 1
      rw [mul_inv]
      ring
  rw [key]
  exact h1.div h2 (fun x => (Real.sqrt_pos.2 (hD x)).ne')

/-- `√ν` is `C^∞` (the explicit `ν` is a smooth transition whose square root is smooth). -/
theorem contDiff_sqrt_nu : ContDiff ℝ ∞ (fun x => √(nu x)) :=
  contDiff_sqrt_smoothTransition.comp (contDiff_const.mul contDiff_id |>.add contDiff_const)

/-! ### The functions `ν_i` and `φ_{J,i}` -/

/-- The profile `ν_i(η) = ν(2^{-i}(η + 1/2)) - ν(η - 1/2)` (the display `nu-functions`, L948-L951
of [O+]), with the explicit `ν`. -/
def nuFamily (i : ℤ) (η : ℝ) : ℝ := nu ((2 : ℝ) ^ (-i) * (η + 1 / 2)) - nu (η - 1 / 2)

/-- The partition function `φ_{J,i}(ξ) = ν((ξ - a)/(2^i (b - a))) - ν((ξ - b)/(b - a))` of the
interval `J = [a, b)` and `i ∈ {-1, 0, 1}` (L942-L946 of [O+]); `J` need not be dyadic. -/
def phiJi (a b : ℝ) (i : ℤ) (ξ : ℝ) : ℝ :=
  nu ((ξ - a) / ((2 : ℝ) ^ i * (b - a))) - nu ((ξ - b) / (b - a))

/-- `φ_{J,i}` for a dyadic interval `J`. -/
def phiDyadic (J : Dyadic) (i : ℤ) : ℝ → ℝ := phiJi J.left J.right i

/-- `φ_{J,i}(ξ) = ν_i((ξ - c(J))/|J|)` (L948-L951 of [O+]). -/
theorem phiJi_eq_nuFamily {a b : ℝ} (hab : a < b) (i : ℤ) (ξ : ℝ) :
    phiJi a b i ξ = nuFamily i ((ξ - (a + b) / 2) / (b - a)) := by
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have h2 : (2 : ℝ) ^ i ≠ 0 := zpow_ne_zero _ (by norm_num)
  unfold phiJi nuFamily
  congr 2
  · rw [zpow_neg]; field_simp; ring
  · field_simp; ring

/-- `φ_{J,i}(ξ) = ν_i((ξ - c(J))/|J|)` for a dyadic interval `J`. -/
theorem phiDyadic_eq_nuFamily (J : Dyadic) (i : ℤ) (ξ : ℝ) :
    phiDyadic J i ξ = nuFamily i ((ξ - J.center) / J.length) := by
  have h := phiJi_eq_nuFamily J.left_lt_right i ξ
  have hR : J.right - J.left = J.length := by rw [Dyadic.right_eq]; ring
  have hC : (J.left + J.right) / 2 = J.center := by rw [Dyadic.center_eq, Dyadic.right_eq]; ring
  rw [hR, hC] at h
  exact h

/-! ### Properties of `ν_i` for `i ≤ 1` -/

/-- `2^{-i} ≥ 1/2` for `i ≤ 1`. -/
theorem two_zpow_neg_ge_half {i : ℤ} (hi : i ≤ 1) : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-i) := by
  have : (2 : ℝ) ^ (-1 : ℤ) ≤ (2 : ℝ) ^ (-i) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  simpa using this

/-- `ν_i` vanishes outside `(-13/25, 51/100)` for `i ≤ 1` (L955-L958 of [O+]). -/
theorem nuFamily_eq_zero {i : ℤ} (hi : i ≤ 1) {η : ℝ}
    (hη : η ≤ -13 / 25 ∨ 51 / 100 ≤ η) : nuFamily i η = 0 := by
  have h2 := two_zpow_neg_ge_half hi
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-i) := zpow_pos (by norm_num) _
  unfold nuFamily
  rcases hη with h | h
  · rw [nu_of_le (x := η - 1 / 2) (by linarith), nu_of_le (by nlinarith)]
    simp
  · rw [nu_of_ge (x := η - 1 / 2) (by linarith), nu_of_ge (by nlinarith)]
    simp

/-- `ν_i ≥ 0` for `i ∈ {-1, 0, 1}`, by monotonicity of `ν`. -/
theorem nuFamily_nonneg {i : ℤ} (hi : -1 ≤ i) (hi' : i ≤ 1) (η : ℝ) : 0 ≤ nuFamily i η := by
  unfold nuFamily
  rw [sub_nonneg]
  have hi2 : i = -1 ∨ i = 0 ∨ i = 1 := by omega
  rcases hi2 with rfl | rfl | rfl
  · -- `2 (η + 1/2) ≥ η - 1/2` unless `η < -3/2`, where both values vanish
    by_cases h : η - 1 / 2 ≤ 2 * (η + 1 / 2)
    · exact monotone_nu (by simpa using h)
    · rw [nu_of_le (x := η - 1 / 2) (by linarith), nu_of_le (by simp; linarith)]
  · exact monotone_nu (by simp; linarith)
  · by_cases h : η - 1 / 2 ≤ (η + 1 / 2) / 2
    · exact monotone_nu (by simpa [div_eq_inv_mul] using h)
    · rw [nu_of_ge (x := η - 1 / 2) (by linarith), nu_of_ge (by simp; linarith)]

/-- `ν_i` is `C^∞`. -/
theorem contDiff_nuFamily (i : ℤ) : ContDiff ℝ ∞ (nuFamily i) := by
  unfold nuFamily
  exact (contDiff_nu.comp (contDiff_const.mul (contDiff_id.add contDiff_const))).sub
    (contDiff_nu.comp (contDiff_id.sub contDiff_const))

/-- `√ν_i` is `C^∞` for `i ≤ 1` (the claim of L955-L958 of [O+], with the explicit `ν`). -/
theorem contDiff_sqrt_nuFamily {i : ℤ} (hi : i ≤ 1) :
    ContDiff ℝ ∞ (fun η => √(nuFamily i η)) := by
  have h2 := two_zpow_neg_ge_half hi
  rw [contDiff_iff_contDiffAt]
  intro η₀
  by_cases h : η₀ < 49 / 100
  · have hev : (fun η => √(nuFamily i η)) =ᶠ[𝓝 η₀]
        fun η => √(nu ((2 : ℝ) ^ (-i) * (η + 1 / 2))) := by
      filter_upwards [Iio_mem_nhds h] with η hη
      simp only [mem_Iio] at hη
      have h0 : nu (η - 1 / 2) = 0 := nu_of_le (by linarith)
      simp only [nuFamily, h0, sub_zero]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (contDiff_sqrt_nu.comp (contDiff_const.mul (contDiff_id.add contDiff_const))).contDiffAt
  · have h : 49 / 100 ≤ η₀ := not_lt.1 h
    have hev : (fun η => √(nuFamily i η)) =ᶠ[𝓝 η₀] fun η => √(nu (1 / 2 - η)) := by
      filter_upwards [Ioi_mem_nhds (show (-12 / 25 : ℝ) < η₀ by linarith)] with η hη
      simp only [mem_Ioi] at hη
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (-i) := zpow_pos (by norm_num) _
      have h1 : nu ((2 : ℝ) ^ (-i) * (η + 1 / 2)) = 1 := nu_of_ge (by nlinarith)
      have h3 : nu (1 / 2 - η) = 1 - nu (η - 1 / 2) := by
        rw [← nu_neg]; congr 1; ring
      simp only [nuFamily, h1, h3]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (contDiff_sqrt_nu.comp (contDiff_const.sub contDiff_id)).contDiffAt

/-! ### Profiles -/

/-- What the wave-packet analysis uses about a frequency profile `χ` (`χ = ν_i`, or its
reflection `ν_i(-·)` of L1119-L1121 of [O+]): it is nonnegative, `√χ` is `C^∞`, and `χ`
vanishes outside `[-13/25, 13/25]`. -/
structure IsProfile (χ : ℝ → ℝ) : Prop where
  nonneg : ∀ η, 0 ≤ χ η
  contDiff_sqrt : ContDiff ℝ ∞ fun η => √(χ η)
  eq_zero : ∀ η : ℝ, η ∉ Icc (-13 / 25 : ℝ) (13 / 25) → χ η = 0

/-- The profile `ν_i` satisfies `IsProfile` for `i ∈ {-1, 0, 1}`. -/
theorem isProfile_nuFamily {i : ℤ} (hi : -1 ≤ i) (hi' : i ≤ 1) : IsProfile (nuFamily i) where
  nonneg := nuFamily_nonneg hi hi'
  contDiff_sqrt := contDiff_sqrt_nuFamily hi'
  eq_zero η hη := by
    refine nuFamily_eq_zero hi' ?_
    simp only [mem_Icc, not_and_or, not_le] at hη
    rcases hη with h | h
    · exact Or.inl h.le
    · exact Or.inr (by linarith)

/-- The reflected profile `η ↦ ν_i(-η)` (L1119-L1121 of [O+]). -/
theorem isProfile_nuFamily_neg {i : ℤ} (hi : -1 ≤ i) (hi' : i ≤ 1) :
    IsProfile (fun η => nuFamily i (-η)) where
  nonneg η := nuFamily_nonneg hi hi' (-η)
  contDiff_sqrt := (contDiff_sqrt_nuFamily hi').comp contDiff_neg
  eq_zero η hη := by
    refine nuFamily_eq_zero hi' ?_
    simp only [mem_Icc, not_and_or, not_le] at hη
    rcases hη with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

/-! ### The support of `φ_{J,i}` -/

/-- `φ_{J,i}` is supported in the `26/25`-dilate of `J` with respect to its center
(L955-L958 of [O+]), for `i ≤ 1`. -/
theorem support_phiDyadic_subset {i : ℤ} (hi : i ≤ 1) (J : Dyadic) :
    Function.support (phiDyadic J i) ⊆ J.dilate (26 / 25) := by
  intro ξ hξ
  rw [Function.mem_support, phiDyadic_eq_nuFamily] at hξ
  have hL := J.length_pos
  set η := (ξ - J.center) / J.length with hη
  have h1 : -13 / 25 < η := by
    by_contra h
    exact hξ (nuFamily_eq_zero hi (Or.inl (not_lt.1 h)))
  have h2 : η < 51 / 100 := by
    by_contra h
    exact hξ (nuFamily_eq_zero hi (Or.inr (not_lt.1 h)))
  have h3 : ξ - J.center = η * J.length := by rw [hη]; field_simp
  unfold Dyadic.dilate
  constructor <;> nlinarith

end PrimeCarleson.Proof.Oplus
