module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Landau
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# A one-sided Landau lemma for entire functions

Part of the de la Vallee Poussin zero-free region (`ZeroFree/Main.lean`). This file proves the local
ingredient: if `F` is entire, bounded by `e^M` on `closedBall c r`, and `‖F c‖ ≥ e^{-A}`, then for
every finite set `S` of zeros of `F` in the disc (all zeros in the disc lying to the left of `c`),

`∑_{ρ ∈ S} (Re 1/(c-ρ) - Re(c-ρ)/r²) ≤ Re F'/F(c) + (232 M + 120 A + 480)/r`

(`landau`).  The proof divides out, one at a time, the zeros of `F` in the disc by Blaschke
factors `r (z - w) / (r² - w̄ z)` (`exists_blaschke`, an induction on the number of zeros counted
with multiplicity), bounds the zero-free quotient `G` by the maximum principle on the circle
(where the Blaschke factors have modulus one), and controls `G'/G` by the existing
`PNTSW.logDeriv_bound_of_disc` (Borel-Caratheodory).  No Jensen formula and no Hadamard product is
needed: every Blaschke term has nonnegative real part.
-/

@[expose] public noncomputable section

open Complex Metric Set

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.ZeroFree


/-- Removing a zero `w` of an entire function:
`F(z) (r² - w̄ z) = r (z - w) F₁(z)` with `F₁` entire. -/
theorem exists_removeZero {r : ℝ} (hr : 0 < r) {F : ℂ → ℂ} (hF : Differentiable ℂ F) {w : ℂ}
    (hw : F w = 0) :
    ∃ F₁ : ℂ → ℂ, Differentiable ℂ F₁ ∧
      ∀ z, F z * ((r : ℂ) ^ 2 - (starRingEnd ℂ) w * z) = (r : ℂ) * (z - w) * F₁ z := by
  have h1 : Differentiable ℂ (dslope F w) := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope Filter.univ_mem).2 hF.differentiableOn
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨fun z => (((r : ℂ) ^ 2 - (starRingEnd ℂ) w * z) / r) * dslope F w z, ?_, ?_⟩
  · fun_prop
  · intro z
    have h := sub_smul_dslope F w z
    simp only [smul_eq_mul, hw, sub_zero] at h
    rw [← h]
    field_simp

/-- On the circle `‖z‖ = r`, `‖r² - w̄ z‖ = r ‖z - w‖` (the Blaschke factor has modulus one). -/
theorem norm_numer_eq {r : ℝ} (w : ℂ) {z : ℂ} (hz : ‖z‖ = r) :
    ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) w * z‖ = r * ‖z - w‖ := by
  have h : (r : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; push_cast; ring
  have h2 : (r : ℂ) ^ 2 - (starRingEnd ℂ) w * z = z * (starRingEnd ℂ) (z - w) := by
    rw [h, map_sub]; ring
  rw [h2, norm_mul, hz, Complex.norm_conj]

/-- The Blaschke denominator `r² - w̄ z` does not vanish for `‖w‖, ‖z‖ < r`. -/
theorem numer_ne_zero {r : ℝ} (hr : 0 < r) {w z : ℂ} (hw : ‖w‖ < r) (hz : ‖z‖ < r) :
    (r : ℂ) ^ 2 - (starRingEnd ℂ) w * z ≠ 0 := by
  intro h
  have h1 : ‖(starRingEnd ℂ) w * z‖ = ‖(r : ℂ) ^ 2‖ := by rw [← sub_eq_zero.mp h]
  rw [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr] at h1
  nlinarith [norm_nonneg w, norm_nonneg z]

/-- An entire function with `F 0 ≠ 0` has finite analytic order everywhere. -/
theorem analyticOrderAt_ne_top_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (z : ℂ) : analyticOrderAt F z ≠ ⊤ := by
  intro h
  rw [analyticOrderAt_eq_top] at h
  have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun x _ => hF.analyticAt x) isPreconnected_univ (mem_univ z) (h.mono fun x hx => hx)
  exact h0 (this (mem_univ 0))

/-- The order bookkeeping of one removal step: `ord F z = [z = w] + ord F₁ z`. -/
theorem ordNat_step {r : ℝ} (hr : 0 < r) {F F₁ : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF₁ : Differentiable ℂ F₁) (h0 : F 0 ≠ 0) (h10 : F₁ 0 ≠ 0) {w : ℂ} (hwr : ‖w‖ < r)
    (hrel : ∀ z, F z * ((r : ℂ) ^ 2 - (starRingEnd ℂ) w * z) = (r : ℂ) * (z - w) * F₁ z)
    {z : ℂ} (hz : ‖z‖ < r) :
    analyticOrderNatAt F z = (if z = w then 1 else 0) + analyticOrderNatAt F₁ z := by
  set u : ℂ → ℂ := fun x => (r : ℂ) ^ 2 - (starRingEnd ℂ) w * x with hu_def
  set c : ℂ → ℂ := fun _ => (r : ℂ) with hc_def
  set g : ℂ → ℂ := fun x => x - w with hg_def
  have hfun : F * u = (c * g) * F₁ := by
    funext x; exact hrel x
  have hu : AnalyticAt ℂ u z := by rw [hu_def]; fun_prop
  have hc : AnalyticAt ℂ c z := analyticAt_const
  have hg : AnalyticAt ℂ g z := by rw [hg_def]; fun_prop
  have hu0 : analyticOrderAt u z = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr (numer_ne_zero hr hwr hz))
  have hc0 : analyticOrderAt c z = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr (by simp [hc_def, hr.ne']))
  have hgn : analyticOrderAt g z = if z = w then 1 else 0 := by
    split_ifs with h
    · rw [h]; exact analyticOrderAt_id_sub_const_self
    · exact analyticOrderAt_id_sub_const_of_ne h
  have hgt : analyticOrderAt g z ≠ ⊤ := by rw [hgn]; split_ifs <;> simp
  have hFt := analyticOrderAt_ne_top_of_entire hF h0 z
  have hF₁t := analyticOrderAt_ne_top_of_entire hF₁ h10 z
  have e1 : analyticOrderNatAt (F * u) z = analyticOrderNatAt F z + analyticOrderNatAt u z :=
    analyticOrderNatAt_mul (hF.analyticAt z) hu hFt (by rw [hu0]; simp)
  have e2 : analyticOrderNatAt (c * g) z = analyticOrderNatAt c z + analyticOrderNatAt g z :=
    analyticOrderNatAt_mul hc hg (by rw [hc0]; simp) hgt
  have e3 : analyticOrderNatAt ((c * g) * F₁) z =
      analyticOrderNatAt (c * g) z + analyticOrderNatAt F₁ z :=
    analyticOrderNatAt_mul (hc.mul hg) (hF₁.analyticAt z)
      (by rw [analyticOrderAt_mul hc hg, hc0, zero_add]; exact hgt) hF₁t
  have hun : analyticOrderNatAt u z = 0 := by simp [analyticOrderNatAt, hu0]
  have hcn : analyticOrderNatAt c z = 0 := by simp [analyticOrderNatAt, hc0]
  have hgn' : analyticOrderNatAt g z = if z = w then 1 else 0 := by
    simp only [analyticOrderNatAt, hgn]; split_ifs <;> simp
  rw [hfun, e3, e2, hcn, hgn'] at e1
  omega

/-- A zero of an entire function with `F 0 ≠ 0` has positive order. -/
theorem ordNat_pos_of_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {z : ℂ}
    (hz : F z = 0) : 0 < analyticOrderNatAt F z := by
  have h1 : analyticOrderAt F z ≠ 0 := (hF.analyticAt z).analyticOrderAt_ne_zero.2 hz
  have h2 := analyticOrderAt_ne_top_of_entire hF h0 z
  have : analyticOrderNatAt F z ≠ 0 := by
    simp [analyticOrderNatAt, ENat.toNat_eq_zero, h1, h2]
  omega

/-- An entire function with `F 0 ≠ 0` has finitely many zeros in any ball around `0`. -/
theorem finite_zeros_ball {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (r : ℝ) :
    {z : ℂ | ‖z‖ < r ∧ F z = 0}.Finite := by
  have hmer : MeromorphicOn F (closedBall (0 : ℂ) r) := fun z _ => (hF.analyticAt z).meromorphicAt
  refine hmer.divisor_ball_support_finite.subset ?_
  rintro z ⟨hz, hFz⟩
  rw [Function.mem_support, MeromorphicOn.divisor_apply (hmer.mono_set ball_subset_closedBall)
    (by simpa using hz), (hF.analyticAt z).meromorphicOrderAt_eq]
  have h1 : analyticOrderAt F z ≠ 0 := (hF.analyticAt z).analyticOrderAt_ne_zero.2 hFz
  have h2 := analyticOrderAt_ne_top_of_entire hF h0 z
  lift analyticOrderAt F z to ℕ using h2 with k hk
  have hk0 : k ≠ 0 := by rintro rfl; exact h1 rfl
  simpa using hk0

/-- The data of a finite Blaschke factorisation of `F` on the disc of radius `r`: `l` lists the
zeros of `F` in the open disc with multiplicity, and `G` is entire, zero-free in the disc, with
`‖G‖ = ‖F‖` on the circle, `‖F 0‖ ≤ ‖G 0‖`, and the logarithmic derivative of `F` at `0` is that of
`G` plus the sum of the Blaschke terms `w̄/r² - 1/w`. -/
structure BlaschkeData (r : ℝ) (F : ℂ → ℂ) (l : List ℂ) (G : ℂ → ℂ) : Prop where
  diff : Differentiable ℂ G
  mem : ∀ w ∈ l, ‖w‖ < r ∧ F w = 0
  complete : ∀ z, ‖z‖ < r → F z = 0 → z ∈ l
  ne_zero : ∀ z, ‖z‖ < r → G z ≠ 0
  norm_eq : ∀ z, ‖z‖ = r → ‖G z‖ = ‖F z‖
  le_zero : ‖F 0‖ ≤ ‖G 0‖
  logDeriv_eq : deriv F 0 / F 0 = deriv G 0 / G 0 +
    (l.map (fun w => (starRingEnd ℂ) w / ((r : ℂ) ^ 2) - 1 / w)).sum

/-- A function with no zeros in the disc is its own factorisation. -/
theorem BlaschkeData.nil {r : ℝ} {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hno : ∀ z, ‖z‖ < r → F z ≠ 0) : BlaschkeData r F [] F where
  diff := hF
  mem := by simp
  complete := fun z hz hFz => absurd hFz (hno z hz)
  ne_zero := hno
  norm_eq := fun _ _ => rfl
  le_zero := le_rfl
  logDeriv_eq := by simp

/-- Adding one removed zero to a factorisation. -/
theorem BlaschkeData.cons {r : ℝ} (hr : 0 < r) {F F₁ G : ℂ → ℂ} {l : List ℂ} {w : ℂ}
    (hF : Differentiable ℂ F) (hF₁ : Differentiable ℂ F₁) (h0 : F 0 ≠ 0) (hwr : ‖w‖ < r)
    (hFw : F w = 0)
    (hrel : ∀ z, F z * ((r : ℂ) ^ 2 - (starRingEnd ℂ) w * z) = (r : ℂ) * (z - w) * F₁ z)
    (hD : BlaschkeData r F₁ l G) : BlaschkeData r F (w :: l) G where
  diff := hD.diff
  mem := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hwr, hFw⟩
    · obtain ⟨h1, h2⟩ := hD.mem x hx
      refine ⟨h1, ?_⟩
      have h3 := hrel x
      rw [h2, mul_zero] at h3
      exact (mul_eq_zero.1 h3).resolve_right (numer_ne_zero hr hwr h1)
  complete := by
    intro z hz hFz
    have h3 := hrel z
    rw [hFz, zero_mul] at h3
    rcases mul_eq_zero.1 h3.symm with h4 | h4
    · have h5 : z = w := by
        have := (mul_eq_zero.1 h4).resolve_left (by exact_mod_cast hr.ne')
        exact sub_eq_zero.1 this
      rw [h5]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hD.complete z hz h4)
  ne_zero := hD.ne_zero
  norm_eq := by
    intro z hz
    rw [hD.norm_eq z hz]
    have h3 := congrArg norm (hrel z)
    rw [norm_mul, norm_mul, norm_mul, norm_numer_eq w hz, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr] at h3
    have hzw : 0 < ‖z - w‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      intro h
      rw [h] at hz
      linarith
    have : r * ‖z - w‖ ≠ 0 := by positivity
    have h4 : (r * ‖z - w‖) * ‖F z‖ = (r * ‖z - w‖) * ‖F₁ z‖ := by linarith
    exact (mul_left_cancel₀ this h4).symm
  le_zero := by
    have h3 := congrArg norm (hrel 0)
    rw [norm_mul, norm_mul, norm_mul, zero_sub, norm_neg] at h3
    simp only [mul_zero, sub_zero, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] at h3
    have h4 : ‖F 0‖ * r ≤ ‖F₁ 0‖ * r := by
      have h5 : r * (‖F 0‖ * r) = r * (‖w‖ * ‖F₁ 0‖) := by nlinarith
      have h6 : ‖F 0‖ * r = ‖w‖ * ‖F₁ 0‖ := mul_left_cancel₀ hr.ne' h5
      rw [h6]
      nlinarith [norm_nonneg (F₁ 0)]
    exact (le_of_mul_le_mul_right h4 hr).trans hD.le_zero
  logDeriv_eq := by
    have hw0 : w ≠ 0 := fun h => h0 (h ▸ hFw)
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have h10 : F₁ 0 ≠ 0 := by
      intro h
      have h' := hrel 0
      rw [h, mul_zero] at h'
      simp only [mul_zero, sub_zero] at h'
      exact h0 ((mul_eq_zero.1 h').resolve_right (pow_ne_zero 2 hr'))
    have hu : HasDerivAt (fun z : ℂ => (r : ℂ) ^ 2 - (starRingEnd ℂ) w * z)
        (-(starRingEnd ℂ) w) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).const_mul ((starRingEnd ℂ) w)).const_sub ((r : ℂ) ^ 2)
      simpa using this
    have hv : HasDerivAt (fun z : ℂ => (r : ℂ) * (z - w)) (r : ℂ) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).sub_const w).const_mul (r : ℂ)
      simpa using this
    have hfun : (fun z => F z * ((r : ℂ) ^ 2 - (starRingEnd ℂ) w * z)) =
        fun z => ((r : ℂ) * (z - w)) * F₁ z := funext hrel
    have key := congrArg (fun f => logDeriv f 0) hfun
    have hu0 : (r : ℂ) ^ 2 - (starRingEnd ℂ) w * 0 ≠ 0 := by
      simpa using pow_ne_zero 2 hr'
    have hv0 : (r : ℂ) * (0 - w) ≠ 0 := mul_ne_zero hr' (by simpa using hw0)
    rw [logDeriv_fun_mul 0 h0 hu0 (hF.differentiableAt) hu.differentiableAt,
      logDeriv_fun_mul 0 hv0 h10 hv.differentiableAt hF₁.differentiableAt,
      logDeriv_apply, logDeriv_apply, logDeriv_apply, logDeriv_apply, hu.deriv, hv.deriv] at key
    have e1 : (r : ℂ) / ((r : ℂ) * (0 - w)) = -1 / w := by field_simp; ring
    have e2 : -(starRingEnd ℂ) w / ((r : ℂ) ^ 2 - (starRingEnd ℂ) w * 0) =
        -((starRingEnd ℂ) w / ((r : ℂ) ^ 2)) := by simp [neg_div]
    rw [e1, e2] at key
    have h7 := hD.logDeriv_eq
    simp only [List.map_cons, List.sum_cons]
    have e3 : (-1 : ℂ) / w = -(1 / w) := by ring
    rw [e3] at key
    linear_combination key + h7

/-- **Finite Blaschke factorisation** of an entire function on a disc, by induction on the number of
zeros counted with multiplicity. -/
theorem exists_blaschke {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∀ (F : ℂ → ℂ) (Z : Finset ℂ), Differentiable ℂ F → F 0 ≠ 0 → (∀ z ∈ Z, ‖z‖ < r) →
      (∀ z, ‖z‖ < r → F z = 0 → z ∈ Z) → ∑ z ∈ Z, analyticOrderNatAt F z ≤ n →
      ∃ (l : List ℂ) (G : ℂ → ℂ), BlaschkeData r F l G := by
  induction n with
  | zero =>
    intro F Z hF h0 hZr hZ hsum
    have hno : ∀ z, ‖z‖ < r → F z ≠ 0 := by
      intro z hz hFz
      have h1 := ordNat_pos_of_zero hF h0 hFz
      have h2 : analyticOrderNatAt F z ≤ ∑ z ∈ Z, analyticOrderNatAt F z :=
        Finset.single_le_sum (f := fun z => analyticOrderNatAt F z)
          (fun _ _ => Nat.zero_le _) (hZ z hz hFz)
      omega
    exact ⟨[], F, BlaschkeData.nil hF hno⟩
  | succ n ih =>
    intro F Z hF h0 hZr hZ hsum
    by_cases hex : ∃ w, ‖w‖ < r ∧ F w = 0
    · obtain ⟨w, hwr, hFw⟩ := hex
      obtain ⟨F₁, hF₁, hrel⟩ := exists_removeZero hr hF hFw
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have h10 : F₁ 0 ≠ 0 := by
        intro h
        have h' := hrel 0
        rw [h, mul_zero] at h'
        simp only [mul_zero, sub_zero] at h'
        exact h0 ((mul_eq_zero.1 h').resolve_right (pow_ne_zero 2 hr'))
      have hZ₁ : ∀ z, ‖z‖ < r → F₁ z = 0 → z ∈ Z := by
        intro z hz hF₁z
        apply hZ z hz
        have h' := hrel z
        rw [hF₁z, mul_zero] at h'
        exact (mul_eq_zero.1 h').resolve_right (numer_ne_zero hr hwr hz)
      have hsum₁ : ∑ z ∈ Z, analyticOrderNatAt F₁ z ≤ n := by
        have hwZ : w ∈ Z := hZ w hwr hFw
        have h' : ∑ z ∈ Z, analyticOrderNatAt F z = 1 + ∑ z ∈ Z, analyticOrderNatAt F₁ z := by
          rw [Finset.sum_congr rfl (fun z hz => ordNat_step hr hF hF₁ h0 h10 hwr hrel (hZr z hz)),
            Finset.sum_add_distrib]
          simp [hwZ]
        omega
      obtain ⟨l, G, hD⟩ := ih F₁ Z hF₁ h10 hZr hZ₁ hsum₁
      exact ⟨w :: l, G, hD.cons hr hF hF₁ h0 hwr hFw hrel⟩
    · push Not at hex
      exact ⟨[], F, BlaschkeData.nil hF hex⟩

/-- A sum of nonnegative terms over distinct elements of a list is at most the sum over the list. -/
theorem sum_finset_le_list_sum {t : ℂ → ℝ} : ∀ (l : List ℂ), (∀ w ∈ l, 0 ≤ t w) →
    ∀ S : Finset ℂ, (∀ x ∈ S, x ∈ l) → ∑ x ∈ S, t x ≤ (l.map t).sum
  | [], _, S, hS => by
      have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => by simpa using hS x hx)
      simp [this]
  | a :: l, ht, S, hS => by
      classical
      have h1 : ∑ x ∈ S.erase a, t x ≤ (l.map t).sum := by
        apply sum_finset_le_list_sum l (fun w hw => ht w (List.mem_cons_of_mem a hw)) (S.erase a)
        intro x hx
        have := hS x (Finset.mem_of_mem_erase hx)
        exact (List.mem_cons.1 this).resolve_left (Finset.ne_of_mem_erase hx)
      have h2 : ∑ x ∈ S, t x ≤ t a + ∑ x ∈ S.erase a, t x := by
        by_cases ha : a ∈ S
        · rw [← Finset.add_sum_erase S t ha]
        · rw [Finset.erase_eq_of_notMem ha]
          have := ht a List.mem_cons_self
          linarith
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- `Re (1/v) - Re v / r² ≥ 0` for `Re v ≥ 0`, `‖v‖ < r`. -/
theorem term_nonneg {r : ℝ} {v : ℂ} (hre : 0 ≤ v.re) (hv : ‖v‖ < r) :
    0 ≤ (1 / v).re - v.re / r ^ 2 := by
  rcases hre.eq_or_lt with h | h
  · have h' : v.re = 0 := h.symm
    simp [one_div, Complex.inv_re, h']
  · have hv0 : 0 < Complex.normSq v := Complex.normSq_pos.2 (by rintro rfl; simp at h)
    have h1 : Complex.normSq v ≤ r ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      have := norm_nonneg v
      nlinarith
    rw [one_div, Complex.inv_re]
    have : v.re / r ^ 2 ≤ v.re / Complex.normSq v := div_le_div_of_nonneg_left h.le hv0 h1
    linarith

/-- Real part of a list sum. -/
theorem re_list_sum_map (f : ℂ → ℂ) : ∀ l : List ℂ,
    ((l.map f).sum).re = (l.map fun w => (f w).re).sum
  | [] => by simp
  | a :: l => by simp [re_list_sum_map f l]

/-- `‖log w‖ ≤ |log ‖w‖| + 4`. -/
theorem norm_log_le_aux (w : ℂ) :
    ‖Complex.log w‖ ≤ |Real.log ‖w‖| + 4 := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log w)
  rw [Complex.log_re] at h1
  have h2 : |(Complex.log w).im| ≤ Real.pi := by rw [Complex.log_im]; exact Complex.abs_arg_le_pi w
  have h3 : Real.pi ≤ 4 := Real.pi_le_four
  linarith

/-- Landau's lemma centered at `0` (see `landau`). -/
theorem landau_centered {F : ℂ → ℂ} (hF : Differentiable ℂ F) {r M A : ℝ} (hr : 0 < r)
    (hM : 0 < M) (hA : 0 ≤ A) (hb : ∀ z, ‖z‖ ≤ r → ‖F z‖ ≤ Real.exp M)
    (hlow : Real.exp (-A) ≤ ‖F 0‖) (hzero : ∀ z, ‖z‖ < r → F z = 0 → z.re ≤ 0)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ‖ρ‖ < r ∧ F ρ = 0) :
    ∑ ρ ∈ S, ((1 / (-ρ)).re - (-ρ).re / r ^ 2) ≤
      (deriv F 0 / F 0).re + (232 * M + 120 * A + 480) / r := by
  have h0 : F 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    exact absurd hlow (not_le.2 (Real.exp_pos _))
  have hfin := finite_zeros_ball hF h0 r
  obtain ⟨l, G, hD⟩ := exists_blaschke hr _ F hfin.toFinset hF h0
    (fun z hz => (hfin.mem_toFinset.1 hz).1) (fun z hz hFz => hfin.mem_toFinset.2 ⟨hz, hFz⟩) le_rfl
  have hGb : ∀ z ∈ ball (0 : ℂ) r, ‖G z‖ ≤ Real.exp M := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r) isBounded_ball
      hD.diff.diffContOnCl (fun y hy => ?_) (subset_closure hz)
    rw [frontier_ball _ hr.ne', mem_sphere_zero_iff_norm] at hy
    rw [hD.norm_eq y hy]
    exact hb y hy.le
  have h0r : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hG0 : G 0 ≠ 0 := hD.ne_zero 0 (by simpa using hr)
  have hG0pos : 0 < ‖G 0‖ := norm_pos_iff.2 hG0
  have hlo : -A ≤ Real.log ‖G 0‖ :=
    (Real.le_log_iff_exp_le hG0pos).2 (hlow.trans hD.le_zero)
  have hhi : Real.log ‖G 0‖ ≤ M :=
    (Real.log_le_iff_le_exp hG0pos).2 (hGb 0 h0r)
  have hm : Complex.exp (Complex.log (G 0)) = G 0 := Complex.exp_log hG0
  have hmA : ‖Complex.log (G 0)‖ ≤ A + M + 4 := by
    refine (norm_log_le_aux _).trans ?_
    have : |Real.log ‖G 0‖| ≤ A + M := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hbd := PrimeCarleson.Proof.Fplus31.PNTSW.logDeriv_bound_of_disc (F := G) (c := 0)
    (m := Complex.log (G 0)) (R := r) (M := M) (A := A + M + 4) hr hM (by linarith)
    hD.diff.differentiableOn (fun z hz => hD.ne_zero z (by simpa using hz)) hGb hm hmA
    (z := 0) (mem_closedBall_self (by positivity))
  set t : ℂ → ℝ := fun w => (1 / (-w)).re - (-w).re / r ^ 2 with ht
  have hterm : ∀ w ∈ l, ((starRingEnd ℂ) w / ((r : ℂ) ^ 2) - 1 / w).re = t w := by
    intro w _
    have e : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [Complex.sub_re, e, Complex.div_ofReal_re, ht]
    simp only [Complex.conj_re, one_div, inv_neg, Complex.neg_re]
    ring
  have hnn : ∀ w ∈ l, 0 ≤ t w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hD.mem w hw
    have h3 := hzero w h1 h2
    exact term_nonneg (v := -w) (by simpa using h3) (by simpa using h1)
  have hsum_le : ∑ ρ ∈ S, t ρ ≤ (l.map t).sum :=
    sum_finset_le_list_sum l hnn S (fun x hx => hD.complete x (hS x hx).1 (hS x hx).2)
  have hre : (deriv F 0 / F 0).re = (deriv G 0 / G 0).re + (l.map t).sum := by
    rw [hD.logDeriv_eq, Complex.add_re, re_list_sum_map]
    congr 1
    exact congrArg List.sum (List.map_congr_left hterm)
  have hG' : -(deriv G 0 / G 0).re ≤ (112 * M + 120 * (A + M + 4)) / r :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hbd)
  have : (112 * M + 120 * (A + M + 4)) / r = (232 * M + 120 * A + 480) / r := by ring_nf
  linarith

/-- **Landau's lemma, one-sided.**  Let `F` be entire, bounded by `e^M` on the closed disc of radius
`r` around `c`, with `‖F c‖ ≥ e^{-A}`, and suppose every zero in the open disc lies to the left of
`c`.  Then for every finite set `S` of zeros in the disc,
`∑_{ρ ∈ S} (Re 1/(c-ρ) - Re(c-ρ)/r²) ≤ Re F'/F(c) + (232 M + 120 A + 480)/r`. -/
theorem landau {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℂ} {r M A : ℝ} (hr : 0 < r)
    (hM : 0 < M) (hA : 0 ≤ A) (hb : ∀ z, ‖z - c‖ ≤ r → ‖F z‖ ≤ Real.exp M)
    (hlow : Real.exp (-A) ≤ ‖F c‖) (hzero : ∀ z, ‖z - c‖ < r → F z = 0 → z.re ≤ c.re)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ‖ρ - c‖ < r ∧ F ρ = 0) :
    ∑ ρ ∈ S, ((1 / (c - ρ)).re - (c - ρ).re / r ^ 2) ≤
      (deriv F c / F c).re + (232 * M + 120 * A + 480) / r := by
  obtain ⟨F', hF'⟩ : ∃ F' : ℂ → ℂ, F' = fun z => F (z + c) := ⟨_, rfl⟩
  have hF'd : Differentiable ℂ F' := by rw [hF']; fun_prop
  have hder : deriv F' 0 = deriv F c := by
    have := deriv_comp_add_const (f := F) (a := c) (x := 0)
    rw [hF']
    simpa using this
  have hval : ∀ z, F' z = F (z + c) := fun z => by rw [hF']
  have key := landau_centered hF'd hr hM hA (fun z hz => by
      rw [hval]; exact hb (z + c) (by simpa using hz))
    (by rw [hval]; simpa using hlow)
    (fun z hz hFz => by
      rw [hval] at hFz
      have := hzero (z + c) (by simpa using hz) hFz
      simpa using this)
    (S.image (fun ρ => ρ - c)) (by
      intro x hx
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨by simpa using (hS ρ hρ).1, by rw [hval]; simpa using (hS ρ hρ).2⟩)
  rw [Finset.sum_image (by intro x _ y _ h; simpa using h), hder, hval] at key
  simpa [neg_sub] using key

end PrimeCarleson.Proof.Fplus31.ZeroFree
