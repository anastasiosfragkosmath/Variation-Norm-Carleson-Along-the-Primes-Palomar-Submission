module

public import PrimeCarleson.Proof.Paper.P7.Sums

/-!
# `c:disc`: the discrete variational Carleson bound for bounded-variation kernels, with dilations

Source: main paper `c:disc`, L2990–L2999. A kernel `K : ℤ → ℂ` is given by its multiplier
`K̂ : ℝ → ℂ` of bounded variation `≤ c₀` supported in the fundamental domain `(-1/2, 1/2]`,
`K(n) = ∫ K̂(ξ) e(nξ) dξ` (the multipliers `K̂_{Q,d}` of `P5/` are of this form). The modulated
dilated sums are `dilSum K̂ Q f x λ = ∑_n f(x - Qn) e(λ n) K(n)`.

* `cdisc_one` (the case `Q = 1` of `c:disc`, L2990, conditional on `hO : OplusVariationBound`): for
  `r > 2`, `r' < p < ∞`, `‖V^r(∑_n f(x - n) e(λ n) K(n) : λ ∈ S)‖_{ℓ^p} ≤ C_{p,r} c₀ ‖f‖_{ℓ^p}` for
  every `S ⊆ [0, 1)`. For `λ ∈ [0, 1)` and `β ∈ (-1/2, 1/2]` the sum over `v` of the Poisson
  summation collapses exactly to `v ∈ {0, 1}`, so the multiplier is `h(β - λ)` with
  `h = K̂ + K̂(· + 1)` (`dilSum_one_eq_chartMult`), and `chart_variation` applies.
* `cdisc_of_oplus` (`c:disc`, L2992–L2999): the same for
  `∑_n f(x - Qn) e(λ n) K(n)`,
  `Q ≥ 1` an integer, with the constant independent of `Q`: the residue classes `x = Qy + a` reduce
  to `Q = 1` for `y ↦ f(Qy + a)`, and the `ℓ^p` norms add up (`eLpNorm_count_dilation`).
* `sup_modulated_of_oplus` (`P7/DiscSup.lean`): since the multiplier vanishes at a far-away
  frequency `λ₀ = 3`, the single-`λ` and maximal bounds
  `‖sup_{λ ∈ S} |∑_n f(x - Qn) e(λ n) K(n)|‖_{ℓ^p} ≲ c₀ ‖f‖_{ℓ^p}` follow from the variation bound.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.MswTransference
  PrimeCarleson.Proof.Goal0

/-! ### Residue classes -/

/-- The residue-class subsequence `y ↦ f(yQ + a)`. -/
def residueSeq (Q : ℕ) (hQ : 1 ≤ Q) (a : ℤ) (f : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.comapDomain (fun y : ℤ => y * (Q : ℤ) + a) f (by
    intro y _ y' _ h
    have hQ' : (Q : ℤ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    have : y * (Q : ℤ) = y' * (Q : ℤ) := by simpa using h
    exact mul_right_cancel₀ hQ' this)

/-- The residue-class subsequence is `y ↦ f(yQ + a)`. -/
theorem residueSeq_apply {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ) (f : ℤ →₀ ℂ) (y : ℤ) :
    residueSeq Q hQ a f y = f (y * (Q : ℤ) + a) := by
  simp [residueSeq, Finsupp.comapDomain_apply]

/-- `∑_n f(Qy + a - Q n) … = ∑_n (f_a)(y - n) …`: the dilated sum at `x = yQ + a` is the
undilated sum of the residue-class subsequence. -/
theorem dilSum_residue {Q : ℕ} (hQ : 1 ≤ Q) (khat : ℝ → ℂ) (f : ℤ →₀ ℂ) (a y : ℤ) (lam : ℝ) :
    dilSum khat (Q : ℤ) f (y * (Q : ℤ) + a) lam = dilSum khat 1 (residueSeq Q hQ a f) y lam := by
  unfold dilSum
  refine tsum_congr fun n => ?_
  rw [residueSeq_apply]
  congr 3
  ring

/-- Sums over `ℤ` split into the residue classes mod `Q`. -/
theorem tsum_residue {Q : ℕ} (hQ : 1 ≤ Q) (F : ℤ → ℝ≥0∞) :
    ∑' x : ℤ, F x = ∑ a : Fin Q, ∑' y : ℤ, F (y * (Q : ℤ) + (a : ℕ)) := by
  have : NeZero Q := ⟨by omega⟩
  rw [← (Int.divModEquiv Q).symm.tsum_eq]
  simp only [Int.divModEquiv_symm_apply]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm, tsum_fintype]

/-- **The `ℓ^p` norms add up over the residue classes**: if every residue class satisfies the
`Q = 1` bound with constant `K`, so does the whole sequence. -/
theorem eLpNorm_count_dilation {p : ℝ} (hp : 0 < p) {Q : ℕ} (hQ : 1 ≤ Q) (V : ℤ → ℝ≥0∞)
    (f : ℤ →₀ ℂ) (K : ℝ≥0∞) (Va : Fin Q → ℤ → ℝ≥0∞)
    (hV : ∀ (a : Fin Q) (y : ℤ), V (y * (Q : ℤ) + (a : ℕ)) = Va a y)
    (hb : ∀ a : Fin Q, eLpNorm (Va a) (ENNReal.ofReal p) Measure.count ≤
      K * eLpNorm (⇑(residueSeq Q hQ (a : ℕ) f)) (ENNReal.ofReal p) Measure.count) :
    eLpNorm V (ENNReal.ofReal p) Measure.count ≤
      K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  have hN : ∀ F : ℤ → ℝ≥0∞, eLpNorm F (ENNReal.ofReal p) Measure.count ^ p = ∑' x, F x ^ p := by
    intro F
    rw [eLpNorm_count_eq_tsum_enn F hp, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne',
      ENNReal.rpow_one]
  have hN' : ∀ g : ℤ →₀ ℂ, eLpNorm (⇑g) (ENNReal.ofReal p) Measure.count ^ p =
      ∑' x, ‖g x‖ₑ ^ p := by
    intro g
    rw [eLpNorm_count_eq_tsum _ hp, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne',
      ENNReal.rpow_one]
  rw [← ENNReal.rpow_le_rpow_iff hp, hN, ENNReal.mul_rpow_of_nonneg _ _ hp.le, hN' f,
    tsum_residue hQ]
  rw [tsum_residue hQ (fun x => ‖f x‖ₑ ^ p), Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 := (ENNReal.rpow_le_rpow_iff hp).2 (hb a)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, hN, hN'] at h1
  simp_rw [hV] at *
  simpa [residueSeq_apply] using h1

/-! ### `c:disc` -/

/-- A kernel multiplier supported in `(-1/2, 1/2]` is supported in the chart `0`. -/
theorem subset_chartSet_zero {khat : ℝ → ℂ}
    (hsupp : ∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2)) :
    ∀ ξ, khat ξ ≠ 0 → ξ ∈ chartSet 0 := fun ξ h => by
  rw [chartSet_zero]
  exact hsupp ξ h

/-- **The case `Q = 1` of `c:disc`** (conditional on `hO`). For
`r > 2`, `r' < p < ∞` there is `C ≥ 0` such that for every measurable `K̂` supported in
`(-1/2, 1/2]` with variation `≤ c₀`, every finitely supported `f` and every `S ⊆ [0, 1)`,
`‖V^r(∑_n f(x - n) e(λ n) K(n) : λ ∈ S)‖_{ℓ^p} ≤ C c₀ ‖f‖_{ℓ^p}`, `K(n) = ∫ K̂(ξ) e(nξ) dξ`.

Source: main paper `c:disc`, L2990. -/
theorem cdisc_one (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (khat : ℝ → ℂ) (c₀ : ℝ), 0 ≤ c₀ → Measurable khat →
      (∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2)) →
      eVariationOn khat Set.univ ≤ ENNReal.ofReal c₀ →
      ∀ (f : ℤ →₀ ℂ) (S : Set ℝ), S ⊆ Set.Ico 0 1 →
        eLpNorm (fun x : ℤ => rVariationOn r S (fun lam => dilSum khat 1 f x lam))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * c₀) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := chart_variation hO hr hp
  refine ⟨2 * C, by positivity, fun khat c₀ hc₀ hk hsupp hvar f S hS => ?_⟩
  have hs : ∀ s, s ∉ Set.Icc (-1 / 2 : ℝ) (1 / 2) → khat s = 0 := fun s hs => by
    by_contra h
    exact hs (Set.Ioc_subset_Icc_self (hsupp s h))
  have hint : Integrable khat :=
    integrable_of_bound_support hk (norm_le_of_eVariationOn hs hc₀ hvar) hs
  have hsh : ∀ s, s ∉ Set.Icc (-3 / 2 : ℝ) (1 / 2) →
      (fun s => khat s + khat (s + 1)) s = 0 := fun s hs' => by
    have h1 : khat s = 0 := hs s fun hmem => hs' ⟨by linarith [hmem.1], hmem.2⟩
    have h2 : khat (s + 1) = 0 := hs (s + 1) fun hmem =>
      hs' ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    simp [h1, h2]
  have hvar2 : eVariationOn (fun s => khat s + khat (s + 1)) Set.univ ≤
      ENNReal.ofReal (2 * c₀) := by
    refine (eVariationOn_add_shift_le khat).trans ?_
    rw [ENNReal.ofReal_mul zero_le_two]
    gcongr
    simp
  have h := hC 0 (fun s => khat s + khat (s + 1)) (-3 / 2) (1 / 2) hsh (2 * c₀) (by positivity)
    hvar2 f S
  have hcongr : ∀ x : ℤ, rVariationOn r S (fun lam => dilSum khat 1 f x lam) =
      rVariationOn r S (chartMult 0 (fun s => khat s + khat (s + 1)) f x) := fun x =>
    rVariationOn_congr fun lam hlam =>
      dilSum_one_eq_chartMult hint (subset_chartSet_zero hsupp) f x (hS hlam).1 (hS hlam).2.le
  have hfun : (fun x : ℤ => rVariationOn r S (fun lam => dilSum khat 1 f x lam)) =
      fun x => rVariationOn r S (chartMult 0 (fun s => khat s + khat (s + 1)) f x) :=
    funext hcongr
  rw [hfun]
  refine h.trans (le_of_eq ?_)
  rw [show 2 * C * c₀ = C * (2 * c₀) by ring]

/-- **`c:disc`** with the dilation (conditional on `hO`): for `r > 2`, `r' < p < ∞` there is `C ≥ 0`
such that for every integer `Q ≥ 1`, every measurable `K̂` supported in `(-1/2, 1/2]` with variation
`≤ c₀`, every finitely supported `f` and every `S ⊆ [0, 1)`,
`‖V^r(∑_n f(x - Qn) e(λ n) K(n) : λ ∈ S)‖_{ℓ^p} ≤ C c₀ ‖f‖_{ℓ^p}`, independently of `Q`. -/
theorem cdisc_of_oplus (hO : OplusVariationBound) {r p : ℝ} (hr : 2 < r) (hp : r / (r - 1) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (khat : ℝ → ℂ) (c₀ : ℝ), 0 ≤ c₀ → Measurable khat →
      (∀ ξ, khat ξ ≠ 0 → ξ ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2)) →
      eVariationOn khat Set.univ ≤ ENNReal.ofReal c₀ →
      ∀ (Q : ℕ), 1 ≤ Q → ∀ (f : ℤ →₀ ℂ) (S : Set ℝ), S ⊆ Set.Ico 0 1 →
        eLpNorm (fun x : ℤ => rVariationOn r S (fun lam => dilSum khat (Q : ℤ) f x lam))
            (ENNReal.ofReal p) Measure.count ≤
          ENNReal.ofReal (C * c₀) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨C, hC0, hC⟩ := cdisc_one hO hr hp
  have hp0 : 0 < p := by linarith [one_le_of_gt_conj hr hp]
  refine ⟨C, hC0, fun khat c₀ hc₀ hk hsupp hvar Q hQ f S hS => ?_⟩
  refine eLpNorm_count_dilation hp0 hQ _ f _
    (fun a y => rVariationOn r S (fun lam => dilSum khat 1 (residueSeq Q hQ (a : ℕ) f) y lam))
    (fun a y => ?_) (fun a => hC khat c₀ hc₀ hk hsupp hvar _ S hS)
  exact congrArg (rVariationOn r S) (funext fun lam => dilSum_residue hQ khat f (a : ℕ) y lam)

end PrimeCarleson.Proof.Paper
