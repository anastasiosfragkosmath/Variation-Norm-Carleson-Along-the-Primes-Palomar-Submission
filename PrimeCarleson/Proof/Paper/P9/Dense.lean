module

public import PrimeCarleson.Proof.Paper.P9.VarTools
public import PrimeCarleson.Proof.Paper.Defs.Basic

/-!
# From finite sets `T ⊂ 𝕋` to all of `𝕋` ("by monotone convergence")

Source: main paper `p:global-shell-var`, L1998 (first reduction): for a continuous family `λ ↦ a(λ)`
the `r`-variation over `[0, 1)` is the supremum of the variations over the dyadic grids
`G_n = {k/2^n : 0 ≤ k < 2^n}` (finite sets, increasing), so an `ℓ²` bound uniform over finite
`T ⊂ [0, 1)` passes to the variation over `𝕋`.

* `rVariationOn_Ico_le_iSup`: `V^ρ(a : [0,1)) ≤ ⨆_n V^ρ(a : G_n)` for continuous `a`;
* `tsum_sq_iSup_le`: `(∑_x (⨆_n F_n(x))²)^{1/2} ≤ B` if `F_n` is increasing in `n` with
  `(∑_x F_n(x)²)^{1/2} ≤ B` for every `n` (monotone convergence for the counting measure on `ℤ`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The dyadic grid `G_n = {k/2^n : 0 ≤ k < 2^n}` of `[0, 1)`. -/
def dyadicGridIo (n : ℕ) : Set ℝ := (fun k : ℕ => (k : ℝ) / 2 ^ n) '' Set.Iio (2 ^ n)

theorem dyadicGridIo_finite (n : ℕ) : (dyadicGridIo n).Finite := (Set.finite_Iio _).image _

theorem dyadicGridIo_subset_Ico (n : ℕ) : dyadicGridIo n ⊆ Set.Ico 0 1 := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  exact_mod_cast hk

theorem dyadicGridIo_mono : Monotone dyadicGridIo := by
  refine monotone_nat_of_le_succ fun n => ?_
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨2 * k, ?_, ?_⟩
  · simp only [Set.mem_Iio] at hk ⊢
    rw [pow_succ]; omega
  · push_cast; rw [pow_succ]; field_simp

/-- **Dyadic approximation of the variation over `[0, 1)`**: for a continuous family and `ρ > 0`,
`V^ρ(a : [0, 1)) ≤ ⨆_n V^ρ(a : G_n)`. -/
theorem rVariationOn_Ico_le_iSup {ρ : ℝ} (_hρ : 0 < ρ) {a : ℝ → ℂ} (ha : Continuous a) :
    rVariationOn ρ (Set.Ico 0 1) a ≤ ⨆ n : ℕ, rVariationOn ρ (dyadicGridIo n) a := by
  refine rVariationOn_le_iff.2 fun J t ht hS => ?_
  -- the approximating chains
  set tn : ℕ → Fin (J + 1) → ℝ := fun n i => (⌊t i * 2 ^ n⌋₊ : ℝ) / 2 ^ n with htn
  have hnn : ∀ i, 0 ≤ t i := fun i => (hS i).1
  have hlt1 : ∀ i, t i < 1 := fun i => (hS i).2
  have hup : ∀ n i, tn n i ≤ t i := by
    intro n i
    simp only [htn]
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by have := hnn i; positivity)
  have hlow : ∀ n i, t i - (1 / 2) ^ n ≤ tn n i := by
    intro n i
    simp only [htn]
    have h1 := Nat.lt_floor_add_one (t i * 2 ^ n)
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [le_div_iff₀ h2, sub_mul, one_div, inv_pow, inv_mul_cancel₀ h2.ne']
    linarith
  have hconv : ∀ i, Tendsto (fun n => tn n i) atTop (𝓝 (t i)) := by
    intro i
    have hl : Tendsto (fun n : ℕ => t i - (1 / 2 : ℝ) ^ n) atTop (𝓝 (t i - 0)) :=
      tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    rw [sub_zero] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (hlow · i) (hup · i)
  have hmem : ∀ n i, tn n i ∈ dyadicGridIo n := by
    intro n i
    refine ⟨⌊t i * 2 ^ n⌋₊, ?_, rfl⟩
    simp only [Set.mem_Iio]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have : t i * 2 ^ n < ((2 ^ n : ℕ) : ℝ) := by
      push_cast
      nlinarith [hlt1 i]
    exact (Nat.floor_lt (by have := hnn i; positivity)).2 this
  have hstrict : ∀ᶠ n in atTop, StrictMono (tn n) := by
    have : ∀ᶠ n in atTop, ∀ i : Fin J, tn n i.castSucc < tn n i.succ := by
      rw [Filter.eventually_all]
      intro i
      exact (hconv i.castSucc).eventually_lt (hconv i.succ) (ht (Fin.castSucc_lt_succ))
    filter_upwards [this] with n hn
    exact Fin.strictMono_iff_lt_succ.2 hn
  -- the limit of the chain sums
  have hlim : Tendsto (fun n => (∑ i : Fin J, ‖a (tn n i.castSucc) - a (tn n i.succ)‖ₑ ^ ρ) ^
      (1 / ρ)) atTop (𝓝 ((∑ i : Fin J, ‖a (t i.castSucc) - a (t i.succ)‖ₑ ^ ρ) ^ (1 / ρ))) := by
    refine (ENNReal.continuous_rpow_const.tendsto _).comp ?_
    refine tendsto_finsetSum _ fun i _ => ?_
    refine (ENNReal.continuous_rpow_const.tendsto _).comp ?_
    have h1 : Tendsto (fun n => a (tn n i.castSucc) - a (tn n i.succ)) atTop
        (𝓝 (a (t i.castSucc) - a (t i.succ))) :=
      ((ha.tendsto _).comp (hconv _)).sub ((ha.tendsto _).comp (hconv _))
    exact (continuous_enorm.tendsto _).comp h1
  refine le_of_tendsto hlim ?_
  filter_upwards [hstrict] with n hn
  have : (∑ i : Fin J, ‖a (tn n i.castSucc) - a (tn n i.succ)‖ₑ ^ ρ) ^ (1 / ρ) ≤
      rVariationOn ρ (dyadicGridIo n) a :=
    le_rVariationOnH (r := ρ) (S := dyadicGridIo n) (c := a) hn (hmem n)
  exact this.trans (le_iSup (fun n => rVariationOn ρ (dyadicGridIo n) a) n)

/-- **Monotone convergence for `ℓ²(ℤ)`**: if `F_n` is increasing in `n` and every `F_n` has
`ℓ²` norm at most `B`, so has `⨆_n F_n`. -/
theorem tsum_sq_iSup_le {F : ℕ → ℤ → ℝ≥0∞} (hmono : Monotone F) {B : ℝ≥0∞}
    (h : ∀ n, (∑' x : ℤ, F n x ^ 2) ^ (1 / 2 : ℝ) ≤ B) :
    (∑' x : ℤ, (⨆ n, F n x) ^ 2) ^ (1 / 2 : ℝ) ≤ B := by
  have h1 : ∀ x : ℤ, (⨆ n, F n x) ^ 2 = ⨆ n, F n x ^ 2 := by
    intro x
    exact Monotone.map_iSup_of_continuousAt (f := fun y : ℝ≥0∞ => y ^ 2)
      (ENNReal.continuous_pow 2).continuousAt (fun a b hab => pow_le_pow_left' hab 2) (by simp)
  simp_rw [h1]
  have h2 := lintegral_iSup (μ := (Measure.count : Measure ℤ)) (f := fun n x => F n x ^ 2)
    (fun n => measurable_from_top) (fun n m hnm x => pow_le_pow_left' (hmono hnm x) 2)
  simp only [lintegral_count] at h2
  rw [h2]
  calc (⨆ n, ∑' x : ℤ, F n x ^ 2) ^ (1 / 2 : ℝ) ≤ (B ^ 2) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow (iSup_le fun n => ?_) (by norm_num)
        calc ∑' x : ℤ, F n x ^ 2 = ((∑' x : ℤ, F n x ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
              (enorm_rpow_half_sq _).symm
          _ ≤ B ^ 2 := by gcongr; exact h n
    _ = B := enorm_sq_rpow_half B

end PrimeCarleson.Proof.Paper
