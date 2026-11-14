module

public import PrimeCarleson.Proof.Paper.Defs.Basic
public import PrimeCarleson.Proof.Goal0.Ramanujan
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The smooth odd dyadic decomposition `ψ` of `1/t`

The paper fixes `ψ ∈ C_c^∞({t : 1/4 < |t| < 1})`, smooth and odd, with
`∑_{k ≥ 1} ψ_k(t) = 1/t` for `|t| ≥ 1`, where `ψ_k(t) := 2^{-k} ψ(t 2^{-k})`
(Source: main paper `s:Prelim`, L609–L612).
Such `ψ` is not unique, so it is packaged as data:

* `psiK ψ k t = 2^{-k} ψ(t 2^{-k})` (`psiK`), the `L¹`-normalized dilation `ψ_{2^k}`
  (`psiK_eq_dilate`);
* `PsiData`: a function `toFun : ℝ → ℝ` that is smooth (`ContDiff ℝ ∞`), odd, with
  `tsupport ⊆ {1/4 < |t| < 1}` and `HasSum (k ↦ ψ_{k+1}(t)) (1/t)` for `|t| ≥ 1`;
  `PsiData.hasCompactSupport` records that `ψ` has compact support;
* the consequences used later: `PsiData.contDiff_psiK`, `PsiData.psiK_odd`,
  `PsiData.psiK_ne_zero` (`ψ_k` is supported in `2^{k-2} < |t| < 2^k`),
  `PsiData.hasSum_psiK_tail` (`∑_{k > K} ψ_k(t) = 1/t` for `|t| ≥ 2^K`);
* **existence of `ψ`**: `PsiData.nonempty : Nonempty PsiData`, by the explicit
  construction `ψ(t) = θ(t)/t`, `θ(u) = θ₊(u) + θ₊(-u)`,
  `θ₊(u) = s(8u - 5/2)(1 - s(4u - 5/2))` for the smooth step `s = Real.smoothTransition`
  (`θ` is an even partition of unity `θ(u) + θ(u/2) = 1` on `[1/2, 1)` supported in
  `5/16 ≤ |u| ≤ 7/8`).

No fixed `ψ` is chosen: later files take `ψ : PsiData` as a variable, as the paper's
"a fixed Schwartz-class bump" is a free parameter.
-/

@[expose] public noncomputable section

open scoped ContDiff

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

/-- The dyadic piece `ψ_k(t) := 2^{-k} ψ(t 2^{-k})` (Source: main paper `s:Prelim`,
L609–L612). -/
def psiK (ψ : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ := ((2 : ℝ) ^ k)⁻¹ * ψ (t * ((2 : ℝ) ^ k)⁻¹)

/-- `ψ_k` is the `L¹`-normalized dilation `ψ_{2^k}` (L568-L571). -/
theorem psiK_eq_dilate (ψ : ℝ → ℝ) (k : ℕ) : psiK ψ k = dilate ((2 : ℝ) ^ k) ψ := by
  funext t
  simp [psiK, dilate, div_eq_mul_inv]

/-- The data of the paper's `ψ` (L609-L612): a smooth odd function with compact support in
`{1/4 < |t| < 1}` such that `∑_{k ≥ 1} ψ_k(t) = 1/t` for `|t| ≥ 1`. -/
structure PsiData where
  /-- The function `ψ`. -/
  toFun : ℝ → ℝ
  /-- `ψ` is smooth. -/
  contDiff : ContDiff ℝ ∞ toFun
  /-- `ψ` is odd. -/
  odd : ∀ t, toFun (-t) = -toFun t
  /-- The closed support of `ψ` lies in `{1/4 < |t| < 1}`. -/
  tsupport_subset : tsupport toFun ⊆ {t : ℝ | 1 / 4 < |t| ∧ |t| < 1}
  /-- `∑_{k ≥ 1} ψ_k(t) = 1/t` for `|t| ≥ 1`. -/
  hasSum_inv : ∀ t : ℝ, 1 ≤ |t| → HasSum (fun k : ℕ => psiK toFun (k + 1) t) (1 / t)

namespace PsiData

variable (ψ : PsiData)

/-- `ψ` has compact support (it lies in `C_c^∞({1/4 < |t| < 1})`). -/
theorem hasCompactSupport : HasCompactSupport ψ.toFun := by
  refine HasCompactSupport.intro (K := Set.Icc (-1) 1) isCompact_Icc fun t ht => ?_
  by_contra h
  have h1 := ψ.tsupport_subset (subset_tsupport _ h)
  simp only [Set.mem_ofPred_eq] at h1
  exact ht (Set.mem_Icc.2 (abs_le.1 h1.2.le))

/-- `ψ(t) ≠ 0` only for `1/4 < |t| < 1`. -/
theorem abs_bounds {t : ℝ} (h : ψ.toFun t ≠ 0) : 1 / 4 < |t| ∧ |t| < 1 :=
  ψ.tsupport_subset (subset_tsupport _ h)

/-- `ψ_k` is smooth. -/
theorem contDiff_psiK (k : ℕ) : ContDiff ℝ ∞ (psiK ψ.toFun k) := by
  rw [psiK_eq_dilate]
  exact contDiff_dilate ψ.contDiff _

/-- `ψ_k` is odd. -/
theorem psiK_odd (k : ℕ) (t : ℝ) : psiK ψ.toFun k (-t) = -psiK ψ.toFun k t := by
  simp only [psiK, neg_mul, ψ.odd]
  ring

/-- `ψ_k(t) ≠ 0` only for `2^{k-2} < |t| < 2^k`. -/
theorem psiK_ne_zero {k : ℕ} {t : ℝ} (h : psiK ψ.toFun k t ≠ 0) :
    (2 : ℝ) ^ k / 4 < |t| ∧ |t| < (2 : ℝ) ^ k := by
  have h2 : ψ.toFun (t * ((2 : ℝ) ^ k)⁻¹) ≠ 0 := fun h0 => h (by simp [psiK, h0])
  obtain ⟨h3, h4⟩ := ψ.abs_bounds h2
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [abs_mul, abs_inv, abs_of_pos hp] at h3 h4
  constructor
  · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [lt_mul_inv_iff₀ hp] at h3
    linarith
  · rwa [mul_inv_lt_iff₀ hp, one_mul] at h4

/-- `ψ_k(t) = 0` for `|t| ≤ 2^k / 4`. -/
theorem psiK_eq_zero_of_le {k : ℕ} {t : ℝ} (h : |t| ≤ (2 : ℝ) ^ k / 4) : psiK ψ.toFun k t = 0 := by
  by_contra h0
  exact absurd (ψ.psiK_ne_zero h0).1 (not_lt.2 h)

/-- `ψ_k(t) = 0` for `|t| ≥ 2^k`. -/
theorem psiK_eq_zero_of_ge {k : ℕ} {t : ℝ} (h : (2 : ℝ) ^ k ≤ |t|) : psiK ψ.toFun k t = 0 := by
  by_contra h0
  exact absurd (ψ.psiK_ne_zero h0).2 (not_lt.2 h)

/-- The tail identity `∑_{k > K} ψ_k(t) = 1/t` for `|t| ≥ 2^K` (all `ψ_k`, `k ≤ K`, vanish). -/
theorem hasSum_psiK_tail (K : ℕ) {t : ℝ} (ht : (2 : ℝ) ^ K ≤ |t|) :
    HasSum (fun k : ℕ => psiK ψ.toFun (k + K + 1) t) (1 / t) := by
  have h1 : 1 ≤ |t| := le_trans (one_le_pow₀ (by norm_num)) ht
  have h2 := ψ.hasSum_inv t h1
  rw [← hasSum_nat_add_iff' K] at h2
  have h3 : ∑ i ∈ Finset.range K, psiK ψ.toFun (i + 1) t = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    refine ψ.psiK_eq_zero_of_ge ?_
    exact le_trans (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hi)) ht
  rw [h3, sub_zero] at h2
  convert h2 using 2

/-- `∑_{k ≥ 1} ψ_k(t) = 1/t` as a `tsum`, for `|t| ≥ 1`. -/
theorem tsum_psiK {t : ℝ} (ht : 1 ≤ |t|) : ∑' k : ℕ, psiK ψ.toFun (k + 1) t = 1 / t :=
  (ψ.hasSum_inv t ht).tsum_eq

end PsiData

/-! ### Construction of `ψ` (Source: main paper `s:Prelim`, L609–L612) -/

namespace PsiConstruction

open Real

/-- The half bump `θ₊(u) = s(8u - 5/2)(1 - s(4u - 5/2))`, `s` the smooth step; supported in
`[5/16, 7/8]`. -/
def bumpPos (u : ℝ) : ℝ := smoothTransition (8 * u - 5 / 2) * (1 - smoothTransition (4 * u - 5 / 2))

/-- The even bump `θ(u) = θ₊(u) + θ₊(-u)`. -/
def bump (u : ℝ) : ℝ := bumpPos u + bumpPos (-u)

/-- The function `ψ(t) = θ(t)/t`. -/
def psiFun (t : ℝ) : ℝ := bump t / t

/-- `θ₊(u) = 0` for `u ≤ 5/16`. -/
theorem bumpPos_eq_zero_of_le {u : ℝ} (h : u ≤ 5 / 16) : bumpPos u = 0 := by
  have : smoothTransition (8 * u - 5 / 2) = 0 := smoothTransition.zero_of_nonpos (by linarith)
  simp [bumpPos, this]

/-- `θ₊(u) = 0` for `u ≥ 7/8`. -/
theorem bumpPos_eq_zero_of_ge {u : ℝ} (h : 7 / 8 ≤ u) : bumpPos u = 0 := by
  have : smoothTransition (4 * u - 5 / 2) = 1 := smoothTransition.one_of_one_le (by linarith)
  simp [bumpPos, this]

/-- `θ₊` is smooth. -/
theorem contDiff_bumpPos : ContDiff ℝ ∞ bumpPos := by
  unfold bumpPos
  have h1 : ContDiff ℝ ∞ (fun u : ℝ => 8 * u - 5 / 2) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun u : ℝ => 4 * u - 5 / 2) := by fun_prop
  exact (smoothTransition.contDiff.comp h1).mul
    (contDiff_const.sub (smoothTransition.contDiff.comp h2))

/-- `θ` is even. -/
theorem bump_neg (u : ℝ) : bump (-u) = bump u := by
  simp [bump, add_comm]

/-- `θ` is smooth. -/
theorem contDiff_bump : ContDiff ℝ ∞ bump := by
  unfold bump
  exact contDiff_bumpPos.add (contDiff_bumpPos.comp contDiff_neg)

/-- `θ(u) = 0` for `|u| ≤ 5/16`. -/
theorem bump_eq_zero_of_abs_le {u : ℝ} (h : |u| ≤ 5 / 16) : bump u = 0 := by
  have h1 := abs_le.1 h
  simp [bump, bumpPos_eq_zero_of_le h1.2, bumpPos_eq_zero_of_le (by linarith [h1.1] : -u ≤ 5 / 16)]

/-- `θ(u) = 0` for `|u| ≥ 7/8`. -/
theorem bump_eq_zero_of_abs_ge {u : ℝ} (h : 7 / 8 ≤ |u|) : bump u = 0 := by
  rcases le_abs'.1 h with h1 | h1
  · simp [bump, bumpPos_eq_zero_of_le (by linarith : u ≤ 5 / 16),
      bumpPos_eq_zero_of_ge (by linarith : 7 / 8 ≤ -u)]
  · simp [bump, bumpPos_eq_zero_of_ge h1, bumpPos_eq_zero_of_le (by linarith : -u ≤ 5 / 16)]

/-- The partition of unity `θ(u) + θ(u/2) = 1` for `u ∈ [1/2, 1)`. -/
theorem bump_add_bump_half {u : ℝ} (h1 : 1 / 2 ≤ u) (h2 : u < 1) : bump u + bump (u / 2) = 1 := by
  have e1 : smoothTransition (8 * u - 5 / 2) = 1 := smoothTransition.one_of_one_le (by linarith)
  have e2 : smoothTransition (2 * u - 5 / 2) = 0 := smoothTransition.zero_of_nonpos (by linarith)
  have e3 : bumpPos (-u) = 0 := bumpPos_eq_zero_of_le (by linarith)
  have e4 : bumpPos (-(u / 2)) = 0 := bumpPos_eq_zero_of_le (by linarith)
  have e5 : bumpPos u = 1 - smoothTransition (4 * u - 5 / 2) := by simp [bumpPos, e1]
  have e6 : bumpPos (u / 2) = smoothTransition (4 * u - 5 / 2) := by
    have : 8 * (u / 2) - 5 / 2 = 4 * u - 5 / 2 := by ring
    have h' : 4 * (u / 2) - 5 / 2 = 2 * u - 5 / 2 := by ring
    simp only [bumpPos, this, h', e2]
    ring
  simp only [bump, e3, e4, e5, e6]
  ring

/-- `ψ` is odd. -/
theorem psiFun_odd (t : ℝ) : psiFun (-t) = -psiFun t := by
  simp [psiFun, bump_neg, div_neg]

/-- `ψ(t) = 0` for `|t| ≤ 5/16` and for `|t| ≥ 7/8`. -/
theorem psiFun_eq_zero {t : ℝ} (h : |t| ≤ 5 / 16 ∨ 7 / 8 ≤ |t|) : psiFun t = 0 := by
  rcases h with h | h
  · simp [psiFun, bump_eq_zero_of_abs_le h]
  · simp [psiFun, bump_eq_zero_of_abs_ge h]

/-- `ψ` is smooth (it vanishes near `0`, where `1/t` is singular). -/
theorem contDiff_psiFun : ContDiff ℝ ∞ psiFun := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hev : psiFun =ᶠ[nhds 0] fun _ => (0 : ℝ) := by
      have : Metric.ball (0 : ℝ) (5 / 16) ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
      filter_upwards [this] with t ht
      refine psiFun_eq_zero (Or.inl ?_)
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht.le
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  · exact contDiff_bump.contDiffAt.div contDiff_id.contDiffAt hx

/-- The sum identity: `∑_{k ≥ 1} ψ_k(t) = 1/t` for `|t| ≥ 1`. -/
theorem hasSum_psiFun {t : ℝ} (ht : 1 ≤ |t|) :
    HasSum (fun k : ℕ => psiK psiFun (k + 1) t) (1 / t) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    linarith
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near ht (by norm_num : (1 : ℝ) < 2)
  have hterm : ∀ k : ℕ, psiK psiFun (k + 1) t = bump (|t| * ((2 : ℝ) ^ (k + 1))⁻¹) / t := by
    intro k
    have hp : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    have hb : bump (|t| * ((2 : ℝ) ^ (k + 1))⁻¹) = bump (t * ((2 : ℝ) ^ (k + 1))⁻¹) := by
      rcases abs_choice t with h | h
      · rw [h]
      · rw [h, neg_mul, bump_neg]
    rw [hb, psiK, psiFun]
    field_simp
  have hzero : ∀ k : ℕ, k ∉ ({m, m + 1} : Finset ℕ) → psiK psiFun (k + 1) t = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have hu : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    rw [hterm]
    rcases lt_or_gt_of_ne hk.1 with hkm | hkm
    · rw [bump_eq_zero_of_abs_ge, zero_div]
      rw [abs_of_nonneg (by positivity)]
      have h1 : (2 : ℝ) ^ (k + 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      have : 1 ≤ |t| * ((2 : ℝ) ^ (k + 1))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hu]
        linarith
      linarith
    · have hk2 : m + 2 ≤ k := by omega
      rw [bump_eq_zero_of_abs_le, zero_div]
      rw [abs_of_nonneg (by positivity), mul_inv_le_iff₀ hu]
      have h1 : (2 : ℝ) ^ (m + 3) ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ (m + 3) = 8 * 2 ^ m := by ring
      have h3 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
      have h4 : (0 : ℝ) < 2 ^ m := by positivity
      rw [h3] at hm2
      nlinarith
  have hfin : HasSum (fun k : ℕ => psiK psiFun (k + 1) t)
      (∑ k ∈ ({m, m + 1} : Finset ℕ), psiK psiFun (k + 1) t) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert hfin using 1
  rw [Finset.sum_pair (by omega : m ≠ m + 1), hterm, hterm, ← add_div]
  have hp : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
  have hu1 : 1 / 2 ≤ |t| * ((2 : ℝ) ^ (m + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    have : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [this]
    linarith
  have hu2 : |t| * ((2 : ℝ) ^ (m + 1))⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hp]
    exact hm2
  have h2 : |t| * ((2 : ℝ) ^ (m + 1 + 1))⁻¹ = (|t| * ((2 : ℝ) ^ (m + 1))⁻¹) / 2 := by
    rw [pow_succ (2 : ℝ) (m + 1)]
    field_simp
  rw [h2, bump_add_bump_half hu1 hu2]

end PsiConstruction

/-- **Existence of `ψ`** (Source: main paper `s:Prelim`, L609–L612): there is a smooth odd
`ψ ∈ C_c^∞({1/4 < |t| < 1})` with
`∑_{k ≥ 1} ψ_k(t) = 1/t` for `|t| ≥ 1`. -/
theorem PsiData.nonempty : Nonempty PsiData := by
  refine ⟨{ toFun := PsiConstruction.psiFun
            contDiff := PsiConstruction.contDiff_psiFun
            odd := PsiConstruction.psiFun_odd
            tsupport_subset := ?_
            hasSum_inv := fun t ht => PsiConstruction.hasSum_psiFun ht }⟩
  have hK : IsClosed {t : ℝ | 5 / 16 ≤ |t| ∧ |t| ≤ 7 / 8} :=
    (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have hsub : Function.support PsiConstruction.psiFun ⊆ {t : ℝ | 5 / 16 ≤ |t| ∧ |t| ≤ 7 / 8} := by
    intro t ht
    by_contra h
    apply ht
    refine PsiConstruction.psiFun_eq_zero ?_
    simp only [Set.mem_ofPred_eq, not_and_or, not_le] at h
    rcases h with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  refine (closure_minimal hsub hK).trans ?_
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]

end PrimeCarleson.Proof.Paper
