module

public import PrimeCarleson.Proof.Paper.Defs.Basic
public import PrimeCarleson.Proof.Common.Variation
public import PrimeCarleson.Proof.Common.VariationDyadic

/-!
# The dilation estimate for the `r`-variation of a 1-periodic family

Source: main paper `e:var-covering-loss`, L1576–L1585: for a 1-periodic scalar family
`(a_λ)_{λ ∈ 𝕋}` and an integer `d ≥ 1`,
`V^r(a_{dλ} : λ ∈ 𝕋) ≲_r d^{1/r} V^r(a_λ : λ ∈ 𝕋) + (∑_{0 ≤ i < d} |a_{i/d}|^r)^{1/r}`.
We prove the stronger inequality without the second term (the covering `λ ↦ dλ` of `𝕋` is
`d`-to-one; the Jones-Seeger-Wright split inequality `rVariationOn_iUnion_le` on the `d` blocks
`[i/d, (i+1)/d)` with the reference points `i/d`, where the family `a_{dλ}` is constant).
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common

/-- **`e:var-covering-loss`, strong form**: for `r ≥ 1`, a `1`-periodic `a : ℝ → ℂ` and `d ≥ 1`,
`V^r(a_{dλ} : λ ∈ [0, 1)) ≤ 3 d^{1/r} V^r(a_λ : λ ∈ [0, 1))`. -/
theorem var_covering_loss_strong {r : ℝ} (hr : 1 ≤ r) {a : ℝ → ℂ} (ha : Function.Periodic a 1)
    {d : ℕ} (hd : 1 ≤ d) :
    rVariationOn r (Set.Ico 0 1) (fun lam => a ((d : ℝ) * lam)) ≤
      ENNReal.ofReal (3 * (d : ℝ) ^ (1 / r)) * rVariationOn r (Set.Ico 0 1) a := by
  classical
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set b : ℝ → ℂ := fun lam => a ((d : ℝ) * lam) with hb
  set Jn : Fin d → Set ℝ := fun i => Set.Ico ((i : ℝ) / d) (((i : ℝ) + 1) / d) with hJn
  have hU : Set.Ico (0 : ℝ) 1 = ⋃ i, Jn i := by
    ext x
    simp only [Set.mem_Ico, Set.mem_iUnion, hJn]
    constructor
    · rintro ⟨h0, h1⟩
      have hx : (d : ℝ) * x < d := by nlinarith
      have hfl : ⌊(d : ℝ) * x⌋₊ < d := by
        exact (Nat.floor_lt (by positivity)).2 hx
      refine ⟨⟨⌊(d : ℝ) * x⌋₊, hfl⟩, ?_, ?_⟩
      · rw [div_le_iff₀ hdpos]
        have := Nat.floor_le (show 0 ≤ (d : ℝ) * x by positivity)
        simpa [mul_comm] using this
      · rw [lt_div_iff₀ hdpos]
        have := Nat.lt_floor_add_one ((d : ℝ) * x)
        simpa [mul_comm] using this
    · rintro ⟨i, h1, h2⟩
      refine ⟨le_trans (by positivity) h1, ?_⟩
      have hi : ((i : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast i.2
      calc x < ((i : ℝ) + 1) / d := h2
        _ ≤ 1 := by rw [div_le_one hdpos]; exact hi
  have hord : ∀ i i' : Fin d, i < i' → ∀ x ∈ Jn i, ∀ y ∈ Jn i', x < y := by
    intro i i' hii' x hx y hy
    have h1 : ((i : ℕ) : ℝ) + 1 ≤ (i' : ℕ) := by exact_mod_cast hii'
    have : ((i : ℝ) + 1) / d ≤ (i' : ℝ) / d := div_le_div_of_nonneg_right h1 hdpos.le
    exact lt_of_lt_of_le hx.2 (this.trans hy.1)
  have hp : ∀ i : Fin d, (i : ℝ) / d ∈ Jn i := fun i =>
    ⟨le_rfl, div_lt_div_of_pos_right (by linarith) hdpos⟩
  have h := rVariationOn_iUnion_le hr Jn hord (fun i => (i : ℝ) / d) hp b
  rw [← hU] at h
  -- the blocks
  have hblock : ∀ i : Fin d, rVariationOn r (Jn i) b ≤ rVariationOn r (Set.Ico 0 1) a := by
    intro i
    rw [rVariationOn_le_iff]
    intro J t ht hS
    have hper : ∀ x : ℝ, a (x - (i : ℕ) * 1) = a x := fun x => ha.sub_nat_mul_eq _
    set t' : Fin (J + 1) → ℝ := fun j => (d : ℝ) * t j - i with ht'
    have ht'mono : StrictMono t' := by
      intro j j' hjj'
      simp only [ht']
      have := ht hjj'
      nlinarith
    have ht'S : ∀ j, t' j ∈ Set.Ico (0 : ℝ) 1 := by
      intro j
      have h1 := hS j
      simp only [hJn, Set.mem_Ico] at h1
      obtain ⟨h1, h2⟩ := h1
      rw [div_le_iff₀ hdpos] at h1
      rw [lt_div_iff₀ hdpos] at h2
      constructor <;> simp only [ht'] <;> nlinarith
    have hval : ∀ j, b (t j) = a (t' j) := by
      intro j
      simp only [hb, ht']
      rw [← hper ((d : ℝ) * t j), mul_one]
    have := MswTransference.le_rVariationOn (r := r) (a := a) ht'mono ht'S
    refine le_trans (le_of_eq ?_) this
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hval, hval]
  -- the reference points
  have hrange : rVariationOn r (Set.range fun i : Fin d => (i : ℝ) / d) b = 0 := by
    refine le_antisymm ?_ zero_le
    rw [rVariationOn_le_iff]
    intro J t ht hS
    have hconst : ∀ x ∈ Set.range fun i : Fin d => (i : ℝ) / d, b x = a 0 := by
      rintro x ⟨i, rfl⟩
      simp only [hb]
      rw [mul_div_cancel₀ _ hdpos.ne']
      simpa using ha.nat_mul_eq (i : ℕ)
    have : ∀ j : Fin J, ‖b (t j.castSucc) - b (t j.succ)‖ₑ ^ r = 0 := by
      intro j
      rw [hconst _ (hS _), hconst _ (hS _), sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos hr0]
    simp only [this, Finset.sum_const_zero]
    exact (ENNReal.zero_rpow_of_pos (one_div_pos.2 hr0)).le
  rw [hrange, add_zero] at h
  refine h.trans ?_
  have hsum : ∑ i : Fin d, rVariationOn r (Jn i) b ^ r ≤
      (d : ℝ≥0∞) * rVariationOn r (Set.Ico 0 1) a ^ r := by
    calc ∑ i : Fin d, rVariationOn r (Jn i) b ^ r
        ≤ ∑ _i : Fin d, rVariationOn r (Set.Ico 0 1) a ^ r :=
          Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hblock i) hr0.le
      _ = (d : ℝ≥0∞) * rVariationOn r (Set.Ico 0 1) a ^ r := by simp
  have h1r : (0 : ℝ) ≤ 1 / r := by positivity
  calc 3 * (∑ i : Fin d, rVariationOn r (Jn i) b ^ r) ^ (1 / r)
      ≤ 3 * ((d : ℝ≥0∞) * rVariationOn r (Set.Ico 0 1) a ^ r) ^ (1 / r) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow hsum h1r) _
    _ = ENNReal.ofReal (3 * (d : ℝ) ^ (1 / r)) * rVariationOn r (Set.Ico 0 1) a := by
        have e1 : ENNReal.ofReal ((d : ℝ) ^ (1 / r)) = (d : ℝ≥0∞) ^ (1 / r) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg hdpos.le h1r, ENNReal.ofReal_natCast]
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1r, ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne',
          ENNReal.rpow_one, ENNReal.ofReal_mul (by norm_num), e1]
        simp [mul_assoc]

end PrimeCarleson.Proof.Paper
