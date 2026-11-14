module

public import PrimeCarleson.Proof.Paper.P9.VarTools
public import PrimeCarleson.Proof.Paper.P9.Carrier

/-!
# Lemma T: truncation

Source: main paper `p:variable` and `l:varcarZ` (the band-limited pieces are not finitely
supported). The variational hypothesis `(V_s)` of `p:variable` is needed for the Fourier-restricted
pieces `F_{a/q}` (and `F_R` of `p:transferprop`), which are in `ℓ²(ℤ)` but not finitely supported,
while `l:varcarZ` is a statement for finitely supported `f`. For a finite index set `T`, a variation
bound for finitely supported `f` extends to every `f ∈ ℓ²(ℤ)` (a density `H ∈ L²` on the chart):

* `variable_truncation_le`: for every finite `s ⊂ ℤ`, with `f = invFZ θ H`,
  `‖V^q(K_t * f : t)‖_{ℓ²} ≤ C ‖f‖_{ℓ²} + 2 ∑_{t ∈ T} ‖m_t‖_∞ ‖f 1_{s^c}‖_{ℓ²}`;
* `variable_truncation`: letting `s ↑ ℤ`, `‖V^q(K_t * f : t)‖_{ℓ²} ≤ C ‖f‖_{ℓ²}`.

The multiplier `m_t` is any measurable function bounded on `ℝ` (the chart); `K_t * f` is
`invFZ θ (m_t H)`. For finitely supported `f` the density is `fourierZ f`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- `ℓ^q ≤ ℓ^1` for finite sums in `ℝ≥0∞`, `1 ≤ q`. -/
theorem rpow_sum_rpow_le_sum {ι : Type*} (S : Finset ι) (a : ι → ℝ≥0∞) {q : ℝ}
    (hq : 1 ≤ q) : (∑ u ∈ S, a u ^ q) ^ (1 / q) ≤ ∑ u ∈ S, a u := by
  classical
  have hq0 : 0 < q := by linarith
  have h := Lp_sum_le_sum S S (fun v i => if i = v then a v else 0) hq
  have e1 : ∀ i ∈ S, ∑ v ∈ S, (if i = v then a v else 0) = a i := by
    intro i hi
    simp [Finset.sum_ite_eq, hi]
  have e1' : ∀ i ∈ S, ∑ v ∈ S, (fun v i => if i = v then a v else 0) v i = a i := by
    intro i hi
    exact e1 i hi
  have e2 : ∀ v ∈ S, (∑ i ∈ S, (if i = v then a v else 0) ^ q) ^ (1 / q) = a v := by
    intro v hv
    rw [Finset.sum_eq_single v]
    · rw [ite_eq_left rfl, ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
    · intro i _ hi
      simp [hi, ENNReal.zero_rpow_of_pos hq0]
    · intro h; exact absurd hv h
  rw [Finset.sum_congr rfl fun i hi => by rw [e1' i hi]] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
  exact e2 v hv

/-- **Minkowski for a finite sum of sequences over `ℤ`** (`p = 2`). -/
theorem tsum_sq_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℤ → ℝ≥0∞) :
    (∑' x : ℤ, (∑ t ∈ S, f t x) ^ 2) ^ (1 / 2 : ℝ) ≤
      ∑ t ∈ S, (∑' x : ℤ, f t x ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    exact (tsum_sq_add_le _ _).trans (add_le_add_right ih _)

/-- The truncation `f 1_s` of a sequence to a finite set, as a finitely supported sequence. -/
def truncFS (f : ℤ → ℂ) (s : Finset ℤ) : ℤ →₀ ℂ :=
  Finsupp.onFinset s (fun x => if x ∈ s then f x else 0) (fun x hx => by
    by_contra h
    exact hx (by simp [h]))

theorem truncFS_apply (f : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    truncFS f s x = if x ∈ s then f x else 0 := rfl

section

variable {θ : ℝ} {T : Set ℝ} {m : ℝ → ℝ → ℂ}

/-- **Lemma T, quantitative form**: see the module docstring. -/
theorem variable_truncation_le (hT : T.Finite) (hm : ∀ t ∈ T, Measurable (m t)) {M : ℝ → ℝ}
    (hb : ∀ t ∈ T, ∀ β, ‖m t β‖ ≤ M t) {q : ℝ} (hq : 1 ≤ q) {C : ℝ}
    (hfin : ∀ f : ℤ →₀ ℂ, (∑' x : ℤ, rVariationOn q T
        (fun t => invFZ θ (fun β => m t β * fourierZ f β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C * l2enorm (⇑f))
    {H : ℝ → ℂ} (hH : ChartL2 θ H) (s : Finset ℤ) :
    (∑' x : ℤ, rVariationOn q T (fun t => invFZ θ (fun β => m t β * H β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal C * l2enorm (invFZ θ H) + 2 * ∑ t ∈ hT.toFinset, ENNReal.ofReal (M t) *
        l2enorm (fun x => if x ∈ s then 0 else invFZ θ H x) := by
  classical
  set f : ℤ → ℂ := invFZ θ H with hf
  set fs : ℤ →₀ ℂ := truncFS f s with hfs
  set Hs : ℝ → ℂ := fourierZ fs with hHs
  have hHsL : ChartL2 θ Hs := chartL2_fourierZ θ fs
  have hDL : ChartL2 θ (fun β => H β - Hs β) := hH.sub hHsL
  have hbM : ∀ t ∈ T, ∀ (H' : ℝ → ℂ) β, ‖m t β * H' β‖ ≤ M t * ‖H' β‖ := by
    intro t ht H' β
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb t ht β) (norm_nonneg _)
  have hM0 : ∀ t ∈ T, 0 ≤ M t := fun t ht => (norm_nonneg _).trans (hb t ht 0)
  have hmHs : ∀ t ∈ T, ChartL2 θ (fun β => m t β * Hs β) := fun t ht =>
    hHsL.mul_of_le (M := M t) (hm t ht).aestronglyMeasurable (hbM t ht Hs)
  have hmD : ∀ t ∈ T, ChartL2 θ (fun β => m t β * (H β - Hs β)) := fun t ht =>
    hDL.mul_of_le (M := M t) (hm t ht).aestronglyMeasurable (hbM t ht _)
  have hsplit : ∀ t ∈ T, ∀ x : ℤ, invFZ θ (fun β => m t β * H β) x =
      invFZ θ (fun β => m t β * Hs β) x + invFZ θ (fun β => m t β * (H β - Hs β)) x := by
    intro t ht x
    rw [← invFZ_add (hmHs t ht) (hmD t ht) x]
    congr 1
    funext β
    ring
  have hTf : (↑hT.toFinset : Set ℝ) = T := hT.coe_toFinset
  -- the pointwise bound
  have hpt : ∀ x : ℤ, rVariationOn q T (fun t => invFZ θ (fun β => m t β * H β) x) ≤
      rVariationOn q T (fun t => invFZ θ (fun β => m t β * Hs β) x) +
        2 * ∑ t ∈ hT.toFinset, ‖invFZ θ (fun β => m t β * (H β - Hs β)) x‖ₑ := by
    intro x
    set hs' : ℝ → ℂ := fun t => invFZ θ (fun β => m t β * Hs β) x with hhs
    set hd' : ℝ → ℂ := fun t => invFZ θ (fun β => m t β * (H β - Hs β)) x with hhd
    have h1 : rVariationOn q T (fun t => invFZ θ (fun β => m t β * H β) x) =
        rVariationOn q T (hs' + hd') := rVariationOn_congr fun t ht => hsplit t ht x
    rw [h1]
    refine (rVariationOn_add_le hq T hs' hd').trans (add_le_add_right ?_ _)
    have h2 := rVariationOn_le_two_mul_sum hT.toFinset hd' hq
    rw [hTf] at h2
    refine h2.trans (mul_le_mul_right ?_ 2)
    exact rpow_sum_rpow_le_sum hT.toFinset (fun u => ‖hd' u‖ₑ) hq
  -- ℓ² norms
  have hsq : ∀ t ∈ T, (∑' x : ℤ, ‖invFZ θ (fun β => m t β * (H β - Hs β)) x‖ₑ ^ 2) ^
      (1 / 2 : ℝ) ≤ ENNReal.ofReal (M t) * l2enorm (fun x => if x ∈ s then 0 else f x) := by
    intro t ht
    have hdens : invFZ θ (fun β => H β - Hs β) = fun x => if x ∈ s then 0 else f x := by
      funext x
      rw [invFZ_sub hH hHsL, hHs, invFZ_fourierZ, hfs, truncFS_apply]
      by_cases hx : x ∈ s <;> simp [hx, hf]
    have := l2enorm_invFZ_mul_le (hM0 t ht) (hm t ht).aestronglyMeasurable
      (hbM t ht (fun β => H β - Hs β)) hDL
    rw [hdens] at this
    exact this
  calc (∑' x : ℤ, rVariationOn q T (fun t => invFZ θ (fun β => m t β * H β) x) ^ 2) ^
        (1 / 2 : ℝ)
      ≤ (∑' x : ℤ, (rVariationOn q T (fun t => invFZ θ (fun β => m t β * Hs β) x) +
          2 * ∑ t ∈ hT.toFinset, ‖invFZ θ (fun β => m t β * (H β - Hs β)) x‖ₑ) ^ 2) ^
          (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun x => by gcongr; exact hpt x) (by norm_num)
    _ ≤ (∑' x : ℤ, rVariationOn q T (fun t => invFZ θ (fun β => m t β * Hs β) x) ^ 2) ^
          (1 / 2 : ℝ) + (∑' x : ℤ, (2 * ∑ t ∈ hT.toFinset,
            ‖invFZ θ (fun β => m t β * (H β - Hs β)) x‖ₑ) ^ 2) ^ (1 / 2 : ℝ) :=
        tsum_sq_add_le _ _
    _ ≤ ENNReal.ofReal C * l2enorm (invFZ θ H) + 2 * ∑ t ∈ hT.toFinset, ENNReal.ofReal (M t) *
        l2enorm (fun x => if x ∈ s then 0 else invFZ θ H x) := by
        refine add_le_add ?_ ?_
        · refine (hfin fs).trans (mul_le_mul_right ?_ _)
          unfold l2enorm
          refine ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun x => ?_) (by norm_num)
          rw [hfs, truncFS_apply]
          by_cases hx : x ∈ s
          · simp [hx, hf]
          · simp [hx]
        · calc (∑' x : ℤ, (2 * ∑ t ∈ hT.toFinset,
                ‖invFZ θ (fun β => m t β * (H β - Hs β)) x‖ₑ) ^ 2) ^ (1 / 2 : ℝ)
              = 2 * (∑' x : ℤ, (∑ t ∈ hT.toFinset,
                ‖invFZ θ (fun β => m t β * (H β - Hs β)) x‖ₑ) ^ 2) ^ (1 / 2 : ℝ) := by
                simp_rw [mul_pow]
                rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
                  enorm_sq_rpow_half]
            _ ≤ 2 * ∑ t ∈ hT.toFinset, ENNReal.ofReal (M t) *
                l2enorm (fun x => if x ∈ s then 0 else f x) := by
                gcongr
                refine (tsum_sq_sum_le hT.toFinset
                  (fun t x => ‖invFZ θ (fun β => m t β * (H β - Hs β)) x‖ₑ)).trans ?_
                exact Finset.sum_le_sum fun t ht => hsq t (hT.mem_toFinset.1 ht)

/-- **Lemma T**: if `‖V^q(K_t * f : t ∈ T)‖_{ℓ²} ≤ C ‖f‖_{ℓ²}` for
every finitely supported `f` (density `f̂ = fourierZ f`), then the same holds for every
`f = invFZ θ H ∈ ℓ²(ℤ)`, `H ∈ L²` on the chart. -/
theorem variable_truncation (hT : T.Finite) (hm : ∀ t ∈ T, Measurable (m t)) {M : ℝ → ℝ}
    (hb : ∀ t ∈ T, ∀ β, ‖m t β‖ ≤ M t) {q : ℝ} (hq : 1 ≤ q) {C : ℝ}
    (hfin : ∀ f : ℤ →₀ ℂ, (∑' x : ℤ, rVariationOn q T
        (fun t => invFZ θ (fun β => m t β * fourierZ f β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal C * l2enorm (⇑f))
    {H : ℝ → ℂ} (hH : ChartL2 θ H) :
    (∑' x : ℤ, rVariationOn q T (fun t => invFZ θ (fun β => m t β * H β) x) ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal C * l2enorm (invFZ θ H) := by
  classical
  set f : ℤ → ℂ := invFZ θ H with hf
  have hfsum : ∑' x : ℤ, ‖f x‖ₑ ^ 2 ≠ ⊤ := by
    rw [hf, tsum_enorm_sq_invFZ hH]; exact ENNReal.ofReal_ne_top
  have htail : Tendsto (fun s : Finset ℤ => ∑' x : ℤ, ‖(if x ∈ s then 0 else f x)‖ₑ ^ 2)
      atTop (𝓝 0) := by
    have h := ENNReal.tendsto_tsum_compl_atTop_zero (f := fun x : ℤ => ‖f x‖ₑ ^ 2) hfsum
    refine h.congr fun s => ?_
    have h1 : (fun x : ℤ => ‖(if x ∈ s then (0 : ℂ) else f x)‖ₑ ^ 2) =
        ((↑s : Set ℤ)ᶜ).indicator (fun x : ℤ => ‖f x‖ₑ ^ 2) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [h1, ← tsum_subtype ((↑s : Set ℤ)ᶜ) (fun x : ℤ => ‖f x‖ₑ ^ 2)]
    rfl
  have hε : Tendsto (fun s : Finset ℤ => l2enorm (fun x => if x ∈ s then 0 else f x)) atTop
      (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp htail
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    exact h
  have hK : (2 * ∑ t ∈ hT.toFinset, ENNReal.ofReal (M t)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top)
  have hlim : Tendsto (fun s : Finset ℤ => ENNReal.ofReal C * l2enorm f + 2 *
      ∑ t ∈ hT.toFinset, ENNReal.ofReal (M t) *
        l2enorm (fun x => if x ∈ s then 0 else f x)) atTop
      (𝓝 (ENNReal.ofReal C * l2enorm f + 0)) := by
    refine tendsto_const_nhds.add ?_
    have h1 : Tendsto (fun s : Finset ℤ => ∑ t ∈ hT.toFinset, ENNReal.ofReal (M t) *
        l2enorm (fun x => if x ∈ s then 0 else f x)) atTop (𝓝 0) := by
      have := tendsto_finsetSum hT.toFinset (fun t _ =>
        ENNReal.Tendsto.const_mul hε (Or.inr ENNReal.ofReal_ne_top) :
          ∀ t ∈ hT.toFinset, Tendsto (fun s : Finset ℤ => ENNReal.ofReal (M t) *
            l2enorm (fun x => if x ∈ s then 0 else f x)) atTop (𝓝 (ENNReal.ofReal (M t) * 0)))
      simpa using this
    have := ENNReal.Tendsto.const_mul h1 (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ⊤))
    simpa using this
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim fun s => variable_truncation_le hT hm hb hq hfin hH s

end

end PrimeCarleson.Proof.Paper
