module

public import PrimeCarleson.Proof.Paper.P7.Disc

/-!
# The multiplier of the discrete Hilbert kernel

`sources/Variational_Carleson.tex` L2939-L2944 (`p:disc`, the kernel `1/n`, `n ≠ 0`). The
multiplier of the kernel `K(n) = 1/n` (`n ≠ 0`), `K(0) = 0`, is the sawtooth
`∑_{n ≠ 0} e(-nξ)/n`; on the
fundamental domain `(-1/2, 1/2)` it is
`K̂_H(ξ) = i π (1 + 2ξ)` for `ξ < 0` and `K̂_H(ξ) = i π (2ξ - 1)` for `ξ ≥ 0`
(`hilbertMult`: `i` times `sawG ξ = π (1 + 2 clamp ξ) - 2π 1_{ξ ≥ 0}`), zero outside. It is a
function
of bounded variation (`eVariationOn_hilbertMult_le`: `V(K̂_H) ≤ 4π`: a monotone ramp of height `2π`
and a jump of `2π`), supported in `(-1/2, 1/2)`, and
`∫ K̂_H(ξ) e(nξ) dξ = 1/n` for `n ≠ 0`, `= 0` for `n = 0` (`integral_hilbertMult_mul_e`). So
`c:disc` for `K̂_H` is `p:disc` (`pdisc_of_oplus`, in `PDisc.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference
  PrimeCarleson.Proof.Goal0 Real

/-- The real sawtooth `π (1 + 2 κ(ξ)) - 2π 1_{ξ ≥ 0}`, `κ` the clamp to `[-1/2, 1/2]`. -/
def sawG (ξ : ℝ) : ℝ :=
  π * (1 + 2 * max (-1 / 2) (min ξ (1 / 2))) - 2 * π * (if 0 ≤ ξ then 1 else 0)

/-- The multiplier of the discrete Hilbert kernel `1/n` on `(-1/2, 1/2)`. -/
def hilbertMult (ξ : ℝ) : ℂ := Complex.I * (sawG ξ : ℂ)

/-- `sawG ξ = 0` for `ξ ≤ -1/2`. -/
theorem sawG_of_le {ξ : ℝ} (h : ξ ≤ -1 / 2) : sawG ξ = 0 := by
  have h1 : min ξ (1 / 2) = ξ := min_eq_left (by linarith)
  have h2 : max (-1 / 2) ξ = -1 / 2 := max_eq_left h
  have h3 : ¬ (0 ≤ ξ) := by linarith
  unfold sawG
  simp only [h1, h2, h3, ↓reduceIte]
  ring

/-- `sawG ξ = 0` for `ξ ≥ 1/2`. -/
theorem sawG_of_ge {ξ : ℝ} (h : 1 / 2 ≤ ξ) : sawG ξ = 0 := by
  have h1 : min ξ (1 / 2) = 1 / 2 := min_eq_right h
  have h2 : max (-1 / 2) (1 / 2 : ℝ) = 1 / 2 := max_eq_right (by norm_num)
  have h3 : 0 ≤ ξ := by linarith
  unfold sawG
  simp only [h1, h2, h3, ↓reduceIte]
  ring

/-- `sawG ξ = π (1 + 2ξ)` on `[-1/2, 0)`. -/
theorem sawG_of_neg {ξ : ℝ} (h1 : -1 / 2 ≤ ξ) (h2 : ξ < 0) : sawG ξ = π * (1 + 2 * ξ) := by
  have h3 : min ξ (1 / 2) = ξ := min_eq_left (by linarith)
  have h4 : max (-1 / 2) ξ = ξ := max_eq_right h1
  have h5 : ¬ (0 ≤ ξ) := not_le.2 h2
  unfold sawG
  simp only [h3, h4, h5, ↓reduceIte]
  ring

/-- `sawG ξ = π (2ξ - 1)` on `[0, 1/2]`. -/
theorem sawG_of_nonneg {ξ : ℝ} (h1 : 0 ≤ ξ) (h2 : ξ ≤ 1 / 2) : sawG ξ = π * (2 * ξ - 1) := by
  have h3 : min ξ (1 / 2) = ξ := min_eq_left h2
  have h4 : max (-1 / 2) ξ = ξ := max_eq_right (by linarith)
  unfold sawG
  simp only [h3, h4, h1, ↓reduceIte]
  ring

/-- `K̂_H` vanishes off `(-1/2, 1/2]`. -/
theorem hilbertMult_support {ξ : ℝ} (h : hilbertMult ξ ≠ 0) : ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
  by_contra hne
  apply h
  have : sawG ξ = 0 := by
    rcases not_and_or.1 hne with h1 | h1
    · exact sawG_of_le (not_lt.1 h1)
    · exact sawG_of_ge (by linarith [not_le.1 h1])
  simp [hilbertMult, this]

/-- `sawG` is measurable. -/
theorem measurable_sawG : Measurable sawG := by
  unfold sawG
  refine Measurable.sub ?_ (measurable_const.mul ?_)
  · exact measurable_const.mul (measurable_const.add (measurable_const.mul
      (measurable_const.max (measurable_id.min measurable_const))))
  · exact Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- `K̂_H` is measurable. -/
theorem measurable_hilbertMult : Measurable hilbertMult :=
  measurable_const.mul (Complex.measurable_ofReal.comp measurable_sawG)

/-- `|sawG| ≤ 2π`. -/
theorem norm_sawG_le (ξ : ℝ) : |sawG ξ| ≤ 2 * π := by
  have h1 : 0 ≤ max (-1 / 2 : ℝ) (min ξ (1 / 2)) + 1 / 2 := by
    have := le_max_left (-1 / 2 : ℝ) (min ξ (1 / 2))
    linarith
  have h2 : max (-1 / 2 : ℝ) (min ξ (1 / 2)) ≤ 1 / 2 := max_le (by norm_num) (min_le_right _ _)
  unfold sawG
  have hπ := Real.pi_pos
  split_ifs <;> rw [abs_le] <;> constructor <;> nlinarith

/-! ### Bounded variation -/

/-- A sum of two functions has variation at most the sum of the variations. -/
theorem eVariationOn_add_le (f g : ℝ → ℂ) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) +
          edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) +
          ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- `c · m(ξ)` with `m` real, monotone with values in `[α, β]` has variation at most
`‖c‖ (β - α)`. -/
theorem eVariationOn_const_mul_monotone_le {m : ℝ → ℝ} (hm : Monotone m) {α β : ℝ}
    (hα : ∀ ξ, α ≤ m ξ) (hβ : ∀ ξ, m ξ ≤ β) (c : ℂ) :
    eVariationOn (fun ξ => c * (m ξ : ℂ)) Set.univ ≤ ENNReal.ofReal (‖c‖ * (β - α)) := by
  refine iSup_le fun ⟨n, u, hu, _⟩ => ?_
  have hterm : ∀ i : ℕ, edist (c * (m (u (i + 1)) : ℂ)) (c * (m (u i) : ℂ)) =
      ENNReal.ofReal (‖c‖ * (m (u (i + 1)) - m (u i))) := by
    intro i
    have h0 : 0 ≤ m (u (i + 1)) - m (u i) := sub_nonneg.2 (hm (hu (Nat.le_succ i)))
    rw [edist_dist, dist_eq_norm, ← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg h0]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (norm_nonneg _)
    (sub_nonneg.2 (hm (hu (Nat.le_succ i))))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => m (u i)) n]
  have := hβ (u n)
  have := hα (u 0)
  exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)

/-- **`K̂_H` has bounded variation**: `V(K̂_H) ≤ 4π` (a monotone ramp of height `2π` and a jump of
`2π`). -/
theorem eVariationOn_hilbertMult_le :
    eVariationOn hilbertMult Set.univ ≤ ENNReal.ofReal (4 * π) := by
  have hπ := Real.pi_pos
  have hfun : hilbertMult = fun ξ =>
      Complex.I * ((π * (1 + 2 * max (-1 / 2) (min ξ (1 / 2))) : ℝ) : ℂ) +
        (-(2 * π * Complex.I)) * ((if 0 ≤ ξ then (1 : ℝ) else 0 : ℝ) : ℂ) := by
    funext ξ
    simp only [hilbertMult, sawG]
    push_cast
    ring
  rw [hfun]
  refine (eVariationOn_add_le _ _ _).trans ?_
  have hmono1 : Monotone fun ξ : ℝ => π * (1 + 2 * max (-1 / 2) (min ξ (1 / 2))) := by
    intro a b hab
    have h := max_le_max (le_refl (-1 / 2 : ℝ)) (min_le_min hab (le_refl (1 / 2 : ℝ)))
    exact mul_le_mul_of_nonneg_left (by linarith) hπ.le
  have hlo1 : ∀ ξ : ℝ, 0 ≤ π * (1 + 2 * max (-1 / 2) (min ξ (1 / 2))) := fun ξ => by
    have h1 : (-1 / 2 : ℝ) ≤ max (-1 / 2) (min ξ (1 / 2)) := le_max_left _ _
    exact mul_nonneg hπ.le (by linarith)
  have hhi1 : ∀ ξ : ℝ, π * (1 + 2 * max (-1 / 2) (min ξ (1 / 2))) ≤ 2 * π := fun ξ => by
    have h2 : max (-1 / 2 : ℝ) (min ξ (1 / 2)) ≤ 1 / 2 :=
      max_le (by norm_num) (min_le_right _ _)
    nlinarith
  have h1 := eVariationOn_const_mul_monotone_le hmono1 hlo1 hhi1 Complex.I
  have hmono2 : Monotone fun ξ : ℝ => if 0 ≤ ξ then (1 : ℝ) else 0 := by
    intro a b hab
    by_cases ha : 0 ≤ a
    · have hb : 0 ≤ b := ha.trans hab
      simp [ha, hb]
    · by_cases hb : 0 ≤ b <;> simp [ha, hb]
  have hlo2 : ∀ ξ : ℝ, (0 : ℝ) ≤ if 0 ≤ ξ then (1 : ℝ) else 0 := fun ξ => by
    by_cases hξ : 0 ≤ ξ <;> simp [hξ]
  have hhi2 : ∀ ξ : ℝ, (if 0 ≤ ξ then (1 : ℝ) else 0) ≤ 1 := fun ξ => by
    by_cases hξ : 0 ≤ ξ <;> simp [hξ]
  have h2 := eVariationOn_const_mul_monotone_le hmono2 hlo2 hhi2 (-(2 * π * Complex.I))
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) (by linarith))
    (mul_nonneg (norm_nonneg _) (by linarith))]
  congr 1
  simp only [Complex.norm_I, norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hπ]
  ring

/-! ### The Fourier coefficients of `K̂_H` -/

/-- `e(t) - e(-t) = 2i sin(2πt)`. -/
theorem e_sub_e_neg (t : ℝ) : e t - e (-t) = ((2 * Real.sin (2 * π * t) : ℝ) : ℂ) * Complex.I := by
  have h1 : e t = Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  have h2 : e (-t) = Complex.exp (((-(2 * π * t) : ℝ) : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- `∫_0^{1/2} 2π (1 - 2x) sin(2π n x) dx = 1/n` for a nonzero integer `n`. -/
theorem integral_ramp_sin {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..(1 / 2), 2 * π * (1 - 2 * x) * Real.sin (2 * π * (n : ℝ) * x) =
      1 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (1 / 2),
      HasDerivAt (fun x : ℝ => -((1 - 2 * x) * Real.cos (2 * π * (n : ℝ) * x)) / (n : ℝ) -
          Real.sin (2 * π * (n : ℝ) * x) / (π * (n : ℝ) ^ 2))
        (2 * π * (1 - 2 * x) * Real.sin (2 * π * (n : ℝ) * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => 2 * π * (n : ℝ) * x) (2 * π * (n : ℝ)) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * π * (n : ℝ))
    have h2 := h1.sin
    have h3 := h1.cos
    have h4 : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) x := by
      simpa using ((hasDerivAt_id x).const_mul 2).const_sub 1
    have h5 := (((h4.mul h3).neg).div_const (n : ℝ)).sub (h2.div_const (π * (n : ℝ) ^ 2))
    convert h5 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hs : Real.sin (2 * π * (n : ℝ) * (1 / 2)) = 0 := by
    have : 2 * π * (n : ℝ) * (1 / 2) = (n : ℝ) * π := by ring
    rw [this]
    exact Real.sin_int_mul_pi n
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, hs]
  field_simp
  ring

/-- The Fourier coefficient of `K̂_H` over `(-1/2, 1/2)` as a ramp-sine integral. -/
theorem integral_hilbertMult_interval (n : ℤ) :
    ∫ ξ in (-1 / 2 : ℝ)..(1 / 2), hilbertMult ξ * e ((n : ℝ) * ξ) =
      ((∫ x in (0 : ℝ)..(1 / 2), 2 * π * (1 - 2 * x) * Real.sin (2 * π * (n : ℝ) * x) :
        ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun ξ => hilbertMult ξ * e ((n : ℝ) * ξ) with hF
  have hFmeas : Measurable F :=
    measurable_hilbertMult.mul (continuous_e.comp (by fun_prop)).measurable
  have hFb : ∀ ξ, ‖F ξ‖ ≤ 2 * π := fun ξ => by
    simp only [hF, hilbertMult, norm_mul, norm_e, Complex.norm_I, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    exact norm_sawG_le ξ
  have hI : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b =>
    intervalIntegrable_of_bound hFmeas.aestronglyMeasurable hFb a b
  have hI' : ∀ a b : ℝ, IntervalIntegrable (fun x => F (-x)) volume a b := fun a b =>
    intervalIntegrable_of_bound (hFmeas.comp measurable_neg).aestronglyMeasurable
      (fun ξ => hFb (-ξ)) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hI _ _) (hI _ _)]
  have hneg : ∫ x in (-1 / 2 : ℝ)..0, F x = ∫ x in (0 : ℝ)..(1 / 2), F (-x) := by
    have h12 : (-1 / 2 : ℝ) = -(1 / 2) := by norm_num
    rw [intervalIntegral.integral_comp_neg (f := F), neg_zero, h12]
  rw [hneg, ← intervalIntegral.integral_add (hI' _ _) (hI _ _)]
  have hcongr : ∫ x in (0 : ℝ)..(1 / 2), (F (-x) + F x) =
      ∫ x in (0 : ℝ)..(1 / 2),
        ((2 * π * (1 - 2 * x) * Real.sin (2 * π * (n : ℝ) * x) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx0 := hx.1
    have hx1 := hx.2
    have e1 : sawG (-x) = π * (1 - 2 * x) := by
      rw [sawG_of_neg (by linarith) (by linarith)]
      ring
    have e2 : sawG x = π * (2 * x - 1) := sawG_of_nonneg hx0.le hx1
    have e3 := e_sub_e_neg ((n : ℝ) * x)
    simp only [hF, hilbertMult, e1, e2]
    have e4 : e ((n : ℝ) * (-x)) = e (-((n : ℝ) * x)) := by rw [mul_neg]
    rw [e4]
    have e6 : 2 * π * (n : ℝ) * x = 2 * π * ((n : ℝ) * x) := by ring
    rw [e6]
    generalize Real.sin (2 * π * ((n : ℝ) * x)) = S at e3 ⊢
    have e5 : e ((n : ℝ) * x) = e (-((n : ℝ) * x)) + ((2 * S : ℝ) : ℂ) * Complex.I := by
      rw [← e3]
      ring
    rw [e5]
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination ((-2 : ℂ) * (π : ℂ) * (1 - 2 * (x : ℂ)) * (S : ℂ)) * hI2
  rw [hcongr, intervalIntegral.integral_ofReal]

/-- **The kernel of the Hilbert multiplier is `1/n`**: `∫ K̂_H(ξ) e(nξ) dξ = 1/n` for `n ≠ 0`
and `0` for `n = 0` (odd symmetry). -/
theorem integral_hilbertMult_mul_e (n : ℤ) :
    ∫ ξ, hilbertMult ξ * e ((n : ℝ) * ξ) = if n = 0 then 0 else 1 / (n : ℂ) := by
  have hzero : ∀ ξ ∉ Set.Ioc (-1 / 2 : ℝ) (1 / 2), hilbertMult ξ * e ((n : ℝ) * ξ) = 0 := by
    intro ξ hξ
    by_contra h
    exact hξ (hilbertMult_support (left_ne_zero_of_mul h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2),
    integral_hilbertMult_interval]
  by_cases hn : n = 0
  · subst hn
    simp
  · simp only [hn, ↓reduceIte]
    rw [integral_ramp_sin hn]
    push_cast
    rfl

end PrimeCarleson.Proof.Paper
