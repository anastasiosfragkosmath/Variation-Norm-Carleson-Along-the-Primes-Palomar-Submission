module

public import PrimeCarleson.Proof.Paper.P6a.Basic
public import PrimeCarleson.Proof.Paper.P6a.Series
public import PrimeCarleson.Proof.Paper.P6a.Triangle

/-!
# The crude `ℓ^s` bound for a weight with dyadic decay

The `K_Q`-replacement error (Source: main paper `p:red-var`, L1504): the error weight `w_Q E_Q` is
not compactly supported, so `l:crude-lambda-var-scale` is applied on the dyadic annuli
`A_j = {2^j ≤ |n| < 2^{j+1}}` and summed: if `|g(n)| ≤ β_j` on `A_j` with `∑_j 2^j β_j < ∞`, then
`‖V^r(∑_n f(x-n) g(n) e(λ n) : λ)‖_{ℓ^s} ≤ C ∑_j 2^j β_j ‖f‖_{ℓ^s}` for `s ≥ r'`
(`2^{(j+1)/r} ‖g 1_{A_j}‖_{ℓ^{r'}} ≲ 2^{(j+1)/r} (2^{j+1})^{1/r'} β_j = 2^{j+1} β_j`;
the term `n = 0` does not depend on `λ`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- The annulus `{n : 2^j ≤ |n| < 2^{j+1}}`. -/
def annulus (j : ℕ) : Finset ℤ :=
  (Finset.Icc (-(2 ^ (j + 1) : ℤ)) (2 ^ (j + 1))).filter fun n => 2 ^ j ≤ n.natAbs ∧
    n.natAbs < 2 ^ (j + 1)

theorem mem_annulus {j : ℕ} {n : ℤ} :
    n ∈ annulus j ↔ 2 ^ j ≤ n.natAbs ∧ n.natAbs < 2 ^ (j + 1) := by
  unfold annulus
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have h2 : (n.natAbs : ℤ) < 2 ^ (j + 1) := by exact_mod_cast h.2
    rw [Int.natCast_natAbs] at h2
    have := abs_lt.1 h2
    exact ⟨⟨by linarith [this.1], by linarith [this.2]⟩, h⟩

theorem card_annulus_le (j : ℕ) : ((annulus j).card : ℝ) ≤ 2 ^ (j + 3) := by
  have h1 : (annulus j).card ≤ (Finset.Icc (-(2 ^ (j + 1) : ℤ)) (2 ^ (j + 1))).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Int.card_Icc] at h1
  have h2 : ((2 ^ (j + 1) : ℤ) + 1 - -(2 ^ (j + 1) : ℤ)).toNat = 2 ^ (j + 2) + 1 := by
    have : ((2 ^ (j + 2) + 1 : ℕ) : ℤ) = (2 ^ (j + 1) : ℤ) + 1 - -(2 ^ (j + 1) : ℤ) := by
      push_cast; ring
    rw [← this, Int.toNat_natCast]
  rw [h2] at h1
  have h3 : (2 : ℕ) ^ (j + 2) + 1 ≤ 2 ^ (j + 3) := by
    have : (1 : ℕ) ≤ 2 ^ (j + 2) := Nat.one_le_two_pow
    calc 2 ^ (j + 2) + 1 ≤ 2 ^ (j + 2) + 2 ^ (j + 2) := by omega
      _ = 2 ^ (j + 3) := by ring
  exact_mod_cast h1.trans h3

/-- The term `n = 0` of the weight does not depend on `λ`: its variation vanishes. -/
theorem varOp_delta_zero {r : ℝ} (hr : 0 < r) (c : ℂ) (f : ℤ →₀ ℂ) (x : ℤ) :
    varOp r (fun n => if n = 0 then c else 0) (⇑f) x = 0 := by
  rw [varOp_eq]
  refine le_antisymm ?_ zero_le
  refine (MswTransference.rVariationOn_le fun J t ht hS => ?_)
  have : ∀ lam, weightedModSum (fun n : ℤ => if n = 0 then c else 0) (⇑f) lam x = f x * c := by
    intro lam
    rw [weightedModSum_eq_sum_of_finsupp]
    rw [Finset.sum_eq_single (0 : ℤ)]
    · simp [Goal0.e_zero]
    · intro n _ hn; simp [hn]
    · intro h
      rw [apply_sub_eq_zero_of_not_mem_suppAt h]
      simp
  simp only [this, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hr, Finset.sum_const_zero]
  exact (ENNReal.zero_rpow_of_pos (one_div_pos.2 hr)).le

/-- **The crude bound with dyadic decay**: if `|g(n)| ≤ β_j` for `n ≠ 0`, `j = ⌊log₂ |n|⌋`, and
`∑_j 2^j β_j < ∞`, then `‖V^r(∑_n f(x-n) g(n) e(λ n) : λ)‖_{ℓ^s} ≤ C ∑_j 2^j β_j ‖f‖_{ℓ^s}` for
`s ≥ r'`, with `C` depending only on `r`. -/
theorem varOp_le_annuli {r : ℝ} (hr : 2 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℤ → ℂ) (β : ℕ → ℝ), (∀ j, 0 ≤ β j) →
      (∀ n : ℤ, n ≠ 0 → ‖g n‖ ≤ β (Nat.log 2 n.natAbs)) →
      Summable (fun j : ℕ => (2 : ℝ) ^ j * β j) → ∀ s : ℝ, r / (r - 1) ≤ s → ∀ f : ℤ →₀ ℂ,
        eLpNorm (varOp r g (⇑f)) (ENNReal.ofReal s) Measure.count ≤
          ENNReal.ofReal (C * ∑' j : ℕ, (2 : ℝ) ^ j * β j) *
            eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
  have hr1 : 0 < r - 1 := by linarith
  set ρ : ℝ := r / (r - 1) with hρ
  have hrr : r.HolderConjugate ρ := Real.HolderConjugate.conjExponent (by linarith)
  have hρ1 : 1 < ρ := hrr.symm.lt
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨C₀, hC₀, hcrude⟩ := crude_lambda_var_scale hr.le hrr
  refine ⟨8 * C₀, by positivity, fun g β hβ hg hsum s hs f => ?_⟩
  have hs1 : 1 ≤ s := hρ1.le.trans hs
  set gj : ℕ → ℤ → ℂ := fun j n => if n ∈ annulus j then g n else 0 with hgj
  -- the pointwise decomposition
  have hpt : ∀ x : ℤ, varOp r g (⇑f) x ≤ ∑' j : ℕ, varOp r (gj j) (⇑f) x := by
    intro x
    set R := (suppAt f x).sup Int.natAbs with hR
    set J : ℕ := R + 1 with hJ
    have hJb : ∀ n ∈ suppAt f x, n.natAbs < 2 ^ J := by
      intro n hn
      have h1 : n.natAbs ≤ R := Finset.le_sup (f := Int.natAbs) hn
      have h2 : J < 2 ^ J := Nat.lt_two_pow_self
      omega
    have hweight : ∀ n ∈ suppAt f x, g n =
        (fun n : ℤ => if n = 0 then g 0 else 0) n + (fun n => ∑ j ∈ Finset.range J, gj j n) n := by
      intro n hn
      change g n = (if n = 0 then g 0 else 0) + ∑ j ∈ Finset.range J, gj j n
      by_cases h0 : n = 0
      · subst h0
        have : ∀ j ∈ Finset.range J, gj j 0 = 0 := fun j _ => by
          simp only [hgj, mem_annulus]
          refine ite_eq_right_iff.2 fun hh => ?_
          exfalso
          have : 2 ^ j ≤ (0 : ℤ).natAbs := hh.1
          have h3 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
          simp at this
        simp [Finset.sum_eq_zero this]
      · have hnpos : 0 < n.natAbs := Int.natAbs_pos.2 h0
        set j₀ := Nat.log 2 n.natAbs with hj₀
        have hj₀mem : n ∈ annulus j₀ := by
          rw [mem_annulus]
          exact ⟨Nat.pow_log_le_self 2 hnpos.ne', Nat.lt_pow_succ_log_self (by norm_num) _⟩
        have hj₀J : j₀ ∈ Finset.range J := by
          rw [Finset.mem_range]
          have h1 : 2 ^ j₀ ≤ n.natAbs := (mem_annulus.1 hj₀mem).1
          have h2 := hJb n hn
          have : 2 ^ j₀ < 2 ^ J := lt_of_le_of_lt h1 h2
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
        rw [Finset.sum_eq_single j₀]
        · simp [hgj, hj₀mem, h0]
        · intro j _ hj
          simp only [hgj]
          refine ite_eq_right_iff.2 fun hh => ?_
          have h1 := (mem_annulus.1 hh)
          have h2 := (mem_annulus.1 hj₀mem)
          have : j = j₀ := by
            have e1 : Nat.log 2 n.natAbs = j :=
              Nat.log_eq_of_pow_le_of_lt_pow h1.1 h1.2
            omega
          exact absurd this hj
        · intro h; exact absurd hj₀J h
    calc varOp r g (⇑f) x
        = varOp r ((fun n : ℤ => if n = 0 then g 0 else 0) +
            (fun n => ∑ j ∈ Finset.range J, gj j n)) (⇑f) x :=
          varOp_congr_of_finsupp f x hweight
      _ ≤ varOp r (fun n : ℤ => if n = 0 then g 0 else 0) (⇑f) x +
          varOp r (fun n => ∑ j ∈ Finset.range J, gj j n) (⇑f) x :=
          varOp_add_weight_le (by linarith) _ _ f x
      _ ≤ 0 + ∑ j ∈ Finset.range J, varOp r (gj j) (⇑f) x := by
          rw [varOp_delta_zero (by linarith)]
          exact add_le_add le_rfl (varOp_sum_weight_le (by linarith) _ _ f x)
      _ ≤ ∑' j : ℕ, varOp r (gj j) (⇑f) x := by
          rw [zero_add]; exact ENNReal.sum_le_tsum _
  -- each annulus
  have hann : ∀ j : ℕ, eLpNorm (varOp r (gj j) (⇑f)) (ENNReal.ofReal s) Measure.count ≤
      ENNReal.ofReal (8 * C₀ * ((2 : ℝ) ^ j * β j)) *
        eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
    intro j
    set N₀ : ℝ := (2 : ℝ) ^ (j + 1) with hN₀
    have hN₀2 : 2 ≤ N₀ := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsupp : ∀ n : ℤ, N₀ < |(n : ℝ)| → gj j n = 0 := by
      intro n hn
      simp only [hgj]
      refine ite_eq_right_iff.2 fun hh => ?_
      have := (mem_annulus.1 hh).2
      have h2 : (n.natAbs : ℝ) < (2 : ℝ) ^ (j + 1) := by exact_mod_cast this
      rw [Nat.cast_natAbs, Int.cast_abs] at h2
      exfalso
      linarith
    have h := (hcrude N₀ hN₀2 (gj j) (⇑f) hsupp s hs1).1 hs
    have hS : ∀ n ∉ annulus j, gj j n = 0 := fun n hn => by simp [hgj, hn]
    have hnorm : eLpNorm (gj j) (ENNReal.ofReal ρ) Measure.count =
        ENNReal.ofReal ((∑ n ∈ annulus j, ‖gj j n‖ ^ ρ) ^ (1 / ρ)) := by
      rw [eLpNorm_count_eq_tsum _ hρ0, tsum_enorm_rpow_eq_ofReal_sum hS hρ0,
        ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
          (by positivity)]
    have hbd : ∀ n ∈ annulus j, ‖gj j n‖ ≤ β j := by
      intro n hn
      have hn0 : n ≠ 0 := by
        intro h0; subst h0
        have := (mem_annulus.1 hn).1
        have h3 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        simp at this
      have hl : Nat.log 2 n.natAbs = j :=
        Nat.log_eq_of_pow_le_of_lt_pow (mem_annulus.1 hn).1 (mem_annulus.1 hn).2
      simp only [hgj, hn, ite_true]
      have := hg n hn0
      rwa [hl] at this
    have hsumρ : ∑ n ∈ annulus j, ‖gj j n‖ ^ ρ ≤ 2 ^ (j + 3) * (β j) ^ ρ := by
      calc ∑ n ∈ annulus j, ‖gj j n‖ ^ ρ ≤ ∑ _n ∈ annulus j, (β j) ^ ρ :=
            Finset.sum_le_sum fun n hn => Real.rpow_le_rpow (norm_nonneg _) (hbd n hn) hρ0.le
        _ = (annulus j).card * (β j) ^ ρ := by simp
        _ ≤ 2 ^ (j + 3) * (β j) ^ ρ :=
            mul_le_mul_of_nonneg_right (card_annulus_le j) (by have := hβ j; positivity)
    have hreal : C₀ * N₀ ^ (1 / r) * (∑ n ∈ annulus j, ‖gj j n‖ ^ ρ) ^ (1 / ρ) ≤
        8 * C₀ * ((2 : ℝ) ^ j * β j) := by
      have hb := hβ j
      have h1 : (∑ n ∈ annulus j, ‖gj j n‖ ^ ρ) ^ (1 / ρ) ≤
          ((2 : ℝ) ^ (j + 3)) ^ (1 / ρ) * β j := by
        calc _ ≤ ((2 : ℝ) ^ (j + 3) * (β j) ^ ρ) ^ (1 / ρ) :=
              Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) hsumρ (by positivity)
          _ = ((2 : ℝ) ^ (j + 3)) ^ (1 / ρ) * β j := by
              rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hb _), ← Real.rpow_mul hb,
                mul_one_div_cancel hρ0.ne', Real.rpow_one]
      have h2 : N₀ ^ (1 / r) ≤ ((2 : ℝ) ^ (j + 3)) ^ (1 / r) :=
        Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
          (by positivity)
      have h3 : ((2 : ℝ) ^ (j + 3)) ^ (1 / r) * ((2 : ℝ) ^ (j + 3)) ^ (1 / ρ) = 2 ^ (j + 3) := by
        rw [← Real.rpow_add (by positivity)]
        have := hrr.inv_add_inv_eq_one
        rw [one_div, one_div, this, Real.rpow_one]
      calc C₀ * N₀ ^ (1 / r) * (∑ n ∈ annulus j, ‖gj j n‖ ^ ρ) ^ (1 / ρ)
          ≤ C₀ * ((2 : ℝ) ^ (j + 3)) ^ (1 / r) * (((2 : ℝ) ^ (j + 3)) ^ (1 / ρ) * β j) := by
            gcongr
        _ = C₀ * (((2 : ℝ) ^ (j + 3)) ^ (1 / r) * ((2 : ℝ) ^ (j + 3)) ^ (1 / ρ)) * β j := by ring
        _ = C₀ * 2 ^ (j + 3) * β j := by rw [h3]
        _ = 8 * C₀ * ((2 : ℝ) ^ j * β j) := by ring
    refine h.trans (mul_le_mul' ?_ le_rfl)
    rw [hnorm, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  -- the sum
  calc eLpNorm (varOp r g (⇑f)) (ENNReal.ofReal s) Measure.count
      ≤ eLpNorm (fun x => ∑' j : ℕ, varOp r (gj j) (⇑f) x) (ENNReal.ofReal s) Measure.count :=
        eLpNorm_count_mono_enn hpt _
    _ ≤ ∑' j : ℕ, eLpNorm (varOp r (gj j) (⇑f)) (ENNReal.ofReal s) Measure.count :=
        eLpNorm_count_tsum_le _ hs1
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (8 * C₀ * ((2 : ℝ) ^ j * β j)) *
          eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := ENNReal.tsum_le_tsum hann
    _ = ENNReal.ofReal (8 * C₀ * ∑' j : ℕ, (2 : ℝ) ^ j * β j) *
          eLpNorm (⇑f) (ENNReal.ofReal s) Measure.count := by
        rw [ENNReal.tsum_mul_right]
        congr 1
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by have := hβ j; positivity)
          (hsum.mul_left _), tsum_mul_left]

end PrimeCarleson.Proof.Paper
