module

public import PrimeCarleson.Proof.Paper.P6a.KQBase

/-!
# The tail kernel `H = ∑_{k ≥ k₀} ψ_k` on `ℝ`

For the crude bound of the `K_Q`-replacement error (Source: main paper `p:red-var`, L1504):
`H(t) = ∑_{k ≥ k₀} ψ_k(t)` is bounded by `2 B 2^{-k₀}`, Lipschitz with constant `(4/3) L 4^{-k₀}`,
and equals `1/t` for `|t| ≥ 2^{k₀}` (`B = sup |ψ|`, `L` the Lipschitz constant of `ψ`);
`psiTailZ ψ k₀ n = H(n)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

variable (ψ : PsiData)

/-- `ψ` is bounded. -/
theorem exists_bound_psi : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |ψ.toFun t| ≤ B := by
  obtain ⟨B, hB⟩ := ψ.hasCompactSupport.exists_bound_of_continuous ψ.contDiff.continuous
  exact ⟨max B 0, le_max_right _ _, fun t => by
    have := hB t
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

/-- `ψ` is Lipschitz. -/
theorem exists_lip_psi : ∃ L : ℝ, 0 ≤ L ∧ ∀ t t', |ψ.toFun t - ψ.toFun t'| ≤ L * |t - t'| := by
  have h1 : ContDiff ℝ 1 ψ.toFun := ψ.contDiff.of_le (by norm_num)
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport ψ.hasCompactSupport h1
    (by norm_num)
  refine ⟨C, C.2, fun t t' => ?_⟩
  have := hC.dist_le_mul t t'
  simpa [Real.dist_eq] using this

variable {ψ}

/-- `|ψ_k| ≤ B 2^{-k}`. -/
theorem abs_psiK_le {B : ℝ} (hB : ∀ t, |ψ.toFun t| ≤ B) (k : ℕ) (t : ℝ) :
    |psiK ψ.toFun k t| ≤ B * ((2 : ℝ) ^ k)⁻¹ := by
  unfold psiK
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
  calc ((2 : ℝ) ^ k)⁻¹ * |ψ.toFun (t * ((2 : ℝ) ^ k)⁻¹)| ≤ ((2 : ℝ) ^ k)⁻¹ * B :=
        mul_le_mul_of_nonneg_left (hB _) (by positivity)
    _ = B * ((2 : ℝ) ^ k)⁻¹ := by ring

/-- `|ψ_k(t) - ψ_k(t')| ≤ L 4^{-k} |t - t'|`. -/
theorem abs_psiK_sub_le {L : ℝ} (hL : ∀ t t', |ψ.toFun t - ψ.toFun t'| ≤ L * |t - t'|) (k : ℕ)
    (t t' : ℝ) : |psiK ψ.toFun k t - psiK ψ.toFun k t'| ≤ L * ((4 : ℝ) ^ k)⁻¹ * |t - t'| := by
  unfold psiK
  have hc : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹ := by positivity
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  have := hL (t * ((2 : ℝ) ^ k)⁻¹) (t' * ((2 : ℝ) ^ k)⁻¹)
  rw [← sub_mul, abs_mul, abs_of_pos hc] at this
  have h4 : ((4 : ℝ) ^ k)⁻¹ = ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
    rw [← mul_inv, ← mul_pow]; norm_num
  rw [h4]
  calc ((2 : ℝ) ^ k)⁻¹ * |ψ.toFun (t * ((2 : ℝ) ^ k)⁻¹) - ψ.toFun (t' * ((2 : ℝ) ^ k)⁻¹)|
      ≤ ((2 : ℝ) ^ k)⁻¹ * (L * (|t - t'| * ((2 : ℝ) ^ k)⁻¹)) :=
        mul_le_mul_of_nonneg_left this hc.le
    _ = _ := by ring

/-- The tail kernel `H(t) = ∑_{k ≥ k₀} ψ_k(t)` on `ℝ`. -/
def Hfn (ψ : PsiData) (k₀ : ℕ) (t : ℝ) : ℝ := ∑' i : ℕ, psiK ψ.toFun (k₀ + i) t

theorem summable_abs_psiK {B : ℝ} (hB : ∀ t, |ψ.toFun t| ≤ B) (k₀ : ℕ) (t : ℝ) :
    Summable fun i : ℕ => |psiK ψ.toFun (k₀ + i) t| := by
  have hg : Summable fun i : ℕ => B * ((2 : ℝ) ^ k₀)⁻¹ * ((1 / 2 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => ?_) hg
  refine (abs_psiK_le hB _ _).trans ?_
  rw [pow_add, mul_inv, one_div, inv_pow]
  have : (B * (((2 : ℝ) ^ k₀)⁻¹ * ((2 : ℝ) ^ i)⁻¹)) = B * ((2 : ℝ) ^ k₀)⁻¹ * ((2 : ℝ) ^ i)⁻¹ := by
    ring
  rw [this]

/-- `|H| ≤ 2 B 2^{-k₀}`. -/
theorem abs_Hfn_le {B : ℝ} (hB : ∀ t, |ψ.toFun t| ≤ B) (k₀ : ℕ) (t : ℝ) :
    |Hfn ψ k₀ t| ≤ 2 * B * ((2 : ℝ) ^ k₀)⁻¹ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hg : Summable fun i : ℕ => B * ((2 : ℝ) ^ k₀)⁻¹ * ((1 / 2 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h1 : |Hfn ψ k₀ t| ≤ ∑' i : ℕ, |psiK ψ.toFun (k₀ + i) t| := by
    have := norm_tsum_le_tsum_norm (f := fun i : ℕ => psiK ψ.toFun (k₀ + i) t)
      (by simpa [Real.norm_eq_abs] using summable_abs_psiK hB k₀ t)
    simpa [Hfn, Real.norm_eq_abs] using this
  refine h1.trans ?_
  have h2 : ∑' i : ℕ, |psiK ψ.toFun (k₀ + i) t| ≤
      ∑' i : ℕ, B * ((2 : ℝ) ^ k₀)⁻¹ * ((1 / 2 : ℝ) ^ i) := by
    refine (summable_abs_psiK hB k₀ t).tsum_le_tsum (fun i => ?_) hg
    refine (abs_psiK_le hB _ _).trans (le_of_eq ?_)
    rw [pow_add, mul_inv, one_div, inv_pow]; ring
  refine h2.trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_two]
  ring

/-- `|H(t) - H(t')| ≤ (4/3) L 4^{-k₀} |t - t'|`. -/
theorem abs_Hfn_sub_le {B L : ℝ} (hB : ∀ t, |ψ.toFun t| ≤ B)
    (hL : ∀ t t', |ψ.toFun t - ψ.toFun t'| ≤ L * |t - t'|) (k₀ : ℕ) (t t' : ℝ) :
    |Hfn ψ k₀ t - Hfn ψ k₀ t'| ≤ 4 / 3 * L * ((4 : ℝ) ^ k₀)⁻¹ * |t - t'| := by
  have hs : ∀ u : ℝ, Summable fun i : ℕ => psiK ψ.toFun (k₀ + i) u := fun u =>
    Summable.of_norm (by simpa [Real.norm_eq_abs] using summable_abs_psiK hB k₀ u)
  have hg : Summable fun i : ℕ => L * ((4 : ℝ) ^ k₀)⁻¹ * |t - t'| * ((1 / 4 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hd : Summable fun i : ℕ => psiK ψ.toFun (k₀ + i) t - psiK ψ.toFun (k₀ + i) t' :=
    (hs t).sub (hs t')
  have h1 : |Hfn ψ k₀ t - Hfn ψ k₀ t'| ≤
      ∑' i : ℕ, |psiK ψ.toFun (k₀ + i) t - psiK ψ.toFun (k₀ + i) t'| := by
    unfold Hfn
    rw [← (hs t).tsum_sub (hs t')]
    have := norm_tsum_le_tsum_norm (f := fun i : ℕ => psiK ψ.toFun (k₀ + i) t -
      psiK ψ.toFun (k₀ + i) t') (by simpa [Real.norm_eq_abs] using hd.abs)
    simpa [Real.norm_eq_abs] using this
  refine h1.trans ?_
  have h2 : ∑' i : ℕ, |psiK ψ.toFun (k₀ + i) t - psiK ψ.toFun (k₀ + i) t'| ≤
      ∑' i : ℕ, L * ((4 : ℝ) ^ k₀)⁻¹ * |t - t'| * ((1 / 4 : ℝ) ^ i) := by
    refine hd.abs.tsum_le_tsum (fun i => ?_) hg
    refine (abs_psiK_sub_le hL _ _ _).trans (le_of_eq ?_)
    rw [pow_add, mul_inv, one_div, inv_pow]; ring
  refine h2.trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num
  ring

/-- `H(t) = 1/t` for `|t| ≥ 2^{k₀}`, `k₀ ≥ 1`. -/
theorem Hfn_eq_inv {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {t : ℝ} (ht : (2 : ℝ) ^ k₀ ≤ |t|) :
    Hfn ψ k₀ t = 1 / t := by
  obtain ⟨K, rfl⟩ : ∃ K, k₀ = K + 1 := ⟨k₀ - 1, by omega⟩
  have h2 : (2 : ℝ) ^ K ≤ |t| := le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) ht
  have := (ψ.hasSum_psiK_tail K h2).tsum_eq
  unfold Hfn
  rw [← this]
  refine tsum_congr fun i => ?_
  congr 1; omega

/-- `∑_{k ≥ k₀} ψ_k(n) = H(n)` on integers. -/
theorem psiTailZ_eq_Hfn (k₀ : ℕ) (n : ℤ) : psiTailZ ψ k₀ n = ((Hfn ψ k₀ (n : ℝ) : ℝ) : ℂ) := by
  unfold psiTailZ Hfn psiKz
  rw [Complex.ofReal_tsum]

end PrimeCarleson.Proof.Paper
