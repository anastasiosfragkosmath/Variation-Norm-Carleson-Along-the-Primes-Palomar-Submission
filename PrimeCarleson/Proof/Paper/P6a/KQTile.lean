module

public import PrimeCarleson.Proof.Paper.P6a.KQHat
public import PrimeCarleson.Proof.Paper.P6a.Hyps
public import PrimeCarleson.Proof.Paper.P6a.Series
public import PrimeCarleson.Proof.Common.FourierZ

/-!
# Tiling a multiplier of bounded variation

`l:varcarZ` (hypothesis `VarCarZ`) needs a multiplier supported in an interval of length `≤ 1/10`.
The error multiplier `KQerr_Q` of the `ℓ²` bound of `KQL2.lean` is a function on `ℝ` of bounded
variation and integrable, with no such support. We cut it with the partition of unity `hat t`,
`t ∈ ℤ` (`P6a/KQHat.lean`): `tile m t = hat t · m`, supported in `((t-1)/20, (t+1)/20)`. This file
proves

* the total variation of a tile: `eVariationOn (tile m t) univ ≤ 3 v_t + 80 H_t` with
  `v_t = V(m; [(t-1)/20, (t+1)/20])` and `H_t = ∫ hat t |m|` (the sup bound
  `sup_{J_t} |m| ≤ 40 H_t + v_t` is an averaging argument against `hat t`);
* `∑_t v_t ≤ 2 V(m)` and `∑_t H_t = ∫ |m|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The left end point `(t-1)/20` of the support of `hat t`. -/
def tileL (t : ℤ) : ℝ := ((t : ℝ) - 1) / 20

/-- The right end point `(t+1)/20` of the support of `hat t`. -/
def tileR (t : ℤ) : ℝ := ((t : ℝ) + 1) / 20

/-- The tile `hat t · m`. -/
def tile (m : ℝ → ℂ) (t : ℤ) (ξ : ℝ) : ℂ := (hat t ξ : ℂ) * m ξ

theorem tileL_lt_tileR (t : ℤ) : tileL t < tileR t := by unfold tileL tileR; linarith

theorem tile_eq_zero (m : ℝ → ℂ) (t : ℤ) {ξ : ℝ} (h : ξ ∉ Ioo (tileL t) (tileR t)) :
    tile m t ξ = 0 := by
  simp [tile, hat_eq_zero (t := t) h]

/-- A function vanishing outside `(a, b)` has the same total variation over `ℝ` as over `[a, b]`. -/
theorem eVariationOn_univ_eq_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (h0 : ∀ x, x ∉ Ioo a b → f x = 0) :
    eVariationOn f univ = eVariationOn f (Icc a b) := by
  have e1 : (Iic a ∪ Icc a b) = Iic b := Set.Iic_union_Icc_eq_Iic hab
  have e2 : (Iic b ∪ Ici b) = univ := Set.Iic_union_Ici
  have hA : eVariationOn f (Iic a) = 0 := by
    refine eVariationOn.constant_on ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [h0 x (fun h => by linarith [h.1, mem_Iic.1 hx]), h0 y (fun h => by
      linarith [h.1, mem_Iic.1 hy])]
  have hB : eVariationOn f (Ici b) = 0 := by
    refine eVariationOn.constant_on ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [h0 x (fun h => by linarith [h.2, mem_Ici.1 hx]), h0 y (fun h => by
      linarith [h.2, mem_Ici.1 hy])]
  have hU1 := eVariationOn.union f (s := Iic a) (t := Icc a b) (x := a) isGreatest_Iic
    (isLeast_Icc hab)
  have hU2 := eVariationOn.union f (s := Iic b) (t := Ici b) (x := b) isGreatest_Iic isLeast_Ici
  rw [e1] at hU1
  rw [e2] at hU2
  rw [hU2, hU1, hA, hB]
  simp

/-- `hat t` is integrable. -/
theorem integrable_hat (t : ℤ) : Integrable (hat t) := by
  refine Integrable.mono' (g := (Icc (tileL t) (tileR t)).indicator (fun _ => (1 : ℝ)))
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp)))
    (continuous_hat t).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  by_cases h : ξ ∈ Icc (tileL t) (tileR t)
  · simp only [h, indicator_of_mem, Real.norm_eq_abs, abs_of_nonneg (hat_nonneg t ξ)]
    exact hat_le_one t ξ
  · rw [indicator_of_notMem h, Real.norm_eq_abs, abs_of_nonneg (hat_nonneg t ξ)]
    have : ξ ∉ Ioo (tileL t) (tileR t) := fun h' => h ⟨h'.1.le, h'.2.le⟩
    rw [hat_eq_zero (t := t) this]

/-- The averaging lower bound `∫ hat t ≥ 1/40`. -/
theorem integral_hat_ge (t : ℤ) : 1 / 40 ≤ ∫ ξ, hat t ξ := by
  have hint := integrable_hat t
  set Y : Set ℝ := Icc ((t : ℝ) / 20 - 1 / 40) ((t : ℝ) / 20 + 1 / 40) with hY
  have h1 : ∫ ξ, Y.indicator (fun _ => (1 / 2 : ℝ)) ξ ≤ ∫ ξ, hat t ξ := by
    refine integral_mono_of_nonneg (ae_of_all _ fun ξ => ?_) hint (ae_of_all _ fun ξ => ?_)
    · exact indicator_nonneg (fun _ _ => by norm_num) ξ
    · by_cases h : ξ ∈ Y
      · rw [indicator_of_mem h]
        obtain ⟨h1, h2⟩ := h
        unfold hat
        refine le_max_of_le_left ?_
        have : |ξ - (t : ℝ) / 20| ≤ 1 / 40 := abs_le.2 ⟨by linarith, by linarith⟩
        linarith
      · rw [indicator_of_notMem h]; exact hat_nonneg t ξ
  refine le_trans (le_of_eq ?_) h1
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le
    (by linarith)]
  simp only [smul_eq_mul]
  ring

/-- `hat t · ‖m‖` is integrable for integrable `m`. -/
theorem integrable_hat_mul_norm {m : ℝ → ℂ} (hm : Integrable m) (t : ℤ) :
    Integrable (fun η => hat t η * ‖m η‖) :=
  hm.norm.bdd_mul (c := 1) (continuous_hat t).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hat_nonneg t x)]; exact hat_le_one t x)

/-- The supremum of `|m|` on the support interval of `hat t`:
`|m(ξ)| ≤ 40 ∫ hat t |m| + V(m; J_t)`. -/
theorem norm_le_of_mem_tile {m : ℝ → ℂ} (hm : Integrable m) (t : ℤ)
    (hV : eVariationOn m (Icc (tileL t) (tileR t)) ≠ ⊤) {ξ : ℝ}
    (hξ : ξ ∈ Icc (tileL t) (tileR t)) :
    ‖m ξ‖ ≤ 40 * (∫ η, hat t η * ‖m η‖) + (eVariationOn m (Icc (tileL t) (tileR t))).toReal := by
  set v := (eVariationOn m (Icc (tileL t) (tileR t))).toReal with hv
  set H := ∫ η, hat t η * ‖m η‖ with hH
  have hpt : ∀ η ∈ Icc (tileL t) (tileR t), ‖m ξ‖ ≤ ‖m η‖ + v := by
    intro η hη
    have h1 := eVariationOn.edist_le m hξ hη
    have h2 : dist (m ξ) (m η) ≤ v := by
      rw [edist_dist] at h1
      exact (ENNReal.ofReal_le_iff_le_toReal hV).1 h1
    rw [dist_eq_norm] at h2
    calc ‖m ξ‖ = ‖m η + (m ξ - m η)‖ := by ring_nf
      _ ≤ ‖m η‖ + ‖m ξ - m η‖ := norm_add_le _ _
      _ ≤ ‖m η‖ + v := by linarith
  have hw := integral_hat_ge t
  have hwint := integrable_hat t
  have hH0 : 0 ≤ H := integral_nonneg fun η => mul_nonneg (hat_nonneg t η) (norm_nonneg _)
  have hI : Integrable (fun η => hat t η * (‖m η‖ + v)) := by
    refine ((integrable_hat_mul_norm hm t).add (hwint.mul_const v)).congr
      (ae_of_all _ fun η => ?_)
    simp only [Pi.add_apply]
    ring
  have hmain : ∫ η, hat t η * ‖m ξ‖ ≤ ∫ η, hat t η * (‖m η‖ + v) := by
    refine integral_mono (hwint.mul_const _) hI fun η => ?_
    by_cases hη : η ∈ Icc (tileL t) (tileR t)
    · exact mul_le_mul_of_nonneg_left (hpt η hη) (hat_nonneg t η)
    · have : η ∉ Ioo (tileL t) (tileR t) := fun h' => hη ⟨h'.1.le, h'.2.le⟩
      simp [hat_eq_zero (t := t) this]
  rw [integral_mul_const, show (fun η => hat t η * (‖m η‖ + v)) =
      fun η => hat t η * ‖m η‖ + hat t η * v by funext η; ring,
    integral_add (integrable_hat_mul_norm hm t) (hwint.mul_const v), integral_mul_const] at hmain
  set w := ∫ η, hat t η with hwdef
  have hw0 : 0 < w := by linarith
  have h3 : ‖m ξ‖ * w ≤ H + v * w := by linarith
  have h4 : ‖m ξ‖ ≤ H / w + v := by
    rw [← sub_le_iff_le_add]
    rw [le_div_iff₀ hw0]
    linarith
  have h5 : H / w ≤ 40 * H := by
    rw [div_le_iff₀ hw0]
    nlinarith
  linarith

/-- **The total variation of a tile**: `V(hat t · m; ℝ) ≤ 3 v_t + 80 H_t`. -/
theorem eVariationOn_tile_le {m : ℝ → ℂ} (hm : Integrable m) (t : ℤ)
    (hV : eVariationOn m (Icc (tileL t) (tileR t)) ≠ ⊤) :
    eVariationOn (tile m t) univ ≤ ENNReal.ofReal (3 * (eVariationOn m (Icc (tileL t)
      (tileR t))).toReal + 80 * ∫ η, hat t η * ‖m η‖) := by
  set v := (eVariationOn m (Icc (tileL t) (tileR t))).toReal with hv
  set H := ∫ η, hat t η * ‖m η‖ with hH
  have hH0 : 0 ≤ H := integral_nonneg fun η => mul_nonneg (hat_nonneg t η) (norm_nonneg _)
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  rw [eVariationOn_univ_eq_Icc (tileL_lt_tileR t).le (fun x hx => tile_eq_zero m t hx)]
  have hfun : tile m t = hat t • m := by
    funext ξ; simp [tile, Complex.real_smul]
  have hsmul := eVariationOn_smul_le (f := hat t) (g := m) (s := Icc (tileL t) (tileR t))
    (C := 1) (D := ENNReal.ofReal (40 * H + v))
    (fun x _ => by
      rw [Real.enorm_eq_ofReal (hat_nonneg t x)]
      exact ENNReal.ofReal_le_one.2 (hat_le_one t x))
    (fun x hx => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_le_of_mem_tile hm t hV hx))
  rw [hfun]
  refine hsmul.trans ?_
  have hVeq : eVariationOn m (Icc (tileL t) (tileR t)) = ENNReal.ofReal v := by
    rw [hv, ENNReal.ofReal_toReal hV]
  have h2 := eVariationOn_hat_le t
  calc 1 * eVariationOn m (Icc (tileL t) (tileR t)) +
        ENNReal.ofReal (40 * H + v) * eVariationOn (hat t) (Icc (tileL t) (tileR t))
      ≤ ENNReal.ofReal v + ENNReal.ofReal (40 * H + v) * 2 := by
        rw [one_mul, hVeq]
        gcongr
        exact h2
    _ = ENNReal.ofReal (3 * v + 80 * H) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add hv0 (by positivity)]
        congr 1; ring

/-- Consecutive intervals of length `1/20` have total variation at most the total variation. -/
theorem sum_range_eVariationOn_le (m : ℝ → ℂ) (T n : ℕ) :
    ∑ k ∈ Finset.range n, eVariationOn m
        (Icc (((k : ℝ) - T) / 20) ((((k + 1 : ℕ) : ℝ) - T) / 20)) ≤ eVariationOn m univ := by
  have hmono : Monotone (fun k : ℕ => ((k : ℝ) - T) / 20) := fun a b hab => by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  rw [eVariationOn.sum' m (I := fun k : ℕ => ((k : ℝ) - T) / 20) hmono]
  exact eVariationOn.mono m (subset_univ _)

/-- A sum over `[-T, T] ⊆ ℤ` as a sum over `range (2T+1)`. -/
theorem sum_Icc_eq_sum_range' {β : Type*} [AddCommMonoid β] (T : ℕ) (F : ℤ → β) :
    ∑ t ∈ Finset.Icc (-(T : ℤ)) T, F t = ∑ k ∈ Finset.range (2 * T + 1), F ((k : ℤ) - T) := by
  refine Finset.sum_nbij' (fun t => (t + T).toNat) (fun k => (k : ℤ) - T) ?_ ?_ ?_ ?_ ?_
  · intro t ht; simp only [Finset.mem_Icc] at ht; simp only [Finset.mem_range]; omega
  · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
  · intro t ht; simp only [Finset.mem_Icc] at ht; omega
  · intro k hk; simp only [Finset.mem_range] at hk; omega
  · intro t ht; simp only [Finset.mem_Icc] at ht
    congr 1; omega

/-- `∑_t V(m; [t/20, (t+1)/20]) ≤ V(m; ℝ)`. -/
theorem tsum_eVariationOn_unit_le (m : ℝ → ℂ) :
    ∑' t : ℤ, eVariationOn m (Icc ((t : ℝ) / 20) (((t : ℝ) + 1) / 20)) ≤ eVariationOn m univ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set T : ℕ := s.sup Int.natAbs with hT
  have hs : s ⊆ Finset.Icc (-(T : ℤ)) T := by
    intro t ht
    have : t.natAbs ≤ T := Finset.le_sup (f := Int.natAbs) ht
    rw [Finset.mem_Icc]; omega
  refine (Finset.sum_le_sum_of_subset hs).trans ?_
  rw [sum_Icc_eq_sum_range']
  refine le_trans (le_of_eq ?_) (sum_range_eVariationOn_le m T (2 * T + 1))
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2 <;> push_cast <;> ring

/-- `∑_t V(m; J_t) ≤ 2 V(m; ℝ)`, `J_t = [(t-1)/20, (t+1)/20]`. -/
theorem tsum_eVariationOn_tile_le (m : ℝ → ℂ) :
    ∑' t : ℤ, eVariationOn m (Icc (tileL t) (tileR t)) ≤ 2 * eVariationOn m univ := by
  set u : ℤ → ℝ≥0∞ := fun t => eVariationOn m (Icc ((t : ℝ) / 20) (((t : ℝ) + 1) / 20)) with hu
  have hsplit : ∀ t : ℤ, eVariationOn m (Icc (tileL t) (tileR t)) = u (t - 1) + u t := by
    intro t
    have h := eVariationOn.Icc_add_Icc m (s := univ) (a := tileL t) (b := (t : ℝ) / 20)
      (c := tileR t) (by unfold tileL; linarith) (by unfold tileR; linarith) (mem_univ _)
    simp only [univ_inter] at h
    rw [← h]
    simp only [hu]
    congr 3
    · push_cast; unfold tileL; ring
    · push_cast; ring
  simp_rw [hsplit]
  rw [ENNReal.tsum_add]
  have h1 : ∑' t : ℤ, u (t - 1) = ∑' t : ℤ, u t := (Equiv.subRight (1 : ℤ)).tsum_eq u
  rw [h1, ← two_mul]
  exact mul_le_mul' le_rfl (tsum_eVariationOn_unit_le m)

/-- `∑_t ∫ hat t |m| = ∫ |m|`. -/
theorem hasSum_hat_integral {m : ℝ → ℂ} (hm : Integrable m) :
    HasSum (fun t : ℤ => ∫ η, hat t η * ‖m η‖) (∫ η, ‖m η‖) := by
  refine hasSum_integral_of_dominated_convergence (fun t η => hat t η * ‖m η‖)
    (fun t => (integrable_hat_mul_norm hm t).1) (fun t => ae_of_all _ fun η => ?_)
    (ae_of_all _ fun η => ((hasSum_hat η).mul_right ‖m η‖).summable) ?_
    (ae_of_all _ fun η => by simpa using (hasSum_hat η).mul_right ‖m η‖)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hat_nonneg t η) (norm_nonneg _))]
  · refine hm.norm.congr (ae_of_all _ fun η => ?_)
    simpa using ((hasSum_hat η).mul_right ‖m η‖).tsum_eq.symm

end PrimeCarleson.Proof.Paper
