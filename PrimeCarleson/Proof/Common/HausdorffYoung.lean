module

public import PrimeCarleson.Proof.Common.Interpolation
public import PrimeCarleson.Proof.Common.FourierZ

/-!
# Hausdorff–Young inequalities on `𝕋` and on `ℤ / K`, with a constant `C(r)`

The Hausdorff–Young inequalities used at `sources/Variational_Carleson.tex` L1127-L1137 (proof of
`e:embed`), for the derivative term and for the endpoint term:

* `hausdorffYoung_T`: `(∫₀¹ |∑_{n ∈ S} b_n e(nξ)|^r dξ)^{1/r} ≤ C_r (∑_{n ∈ S} |b_n|^{r'})^{1/r'}`;
* `hausdorffYoung_cyclic`:
  `(∑_{s < K} |∑_{l < K} B_l e(sl/K)|^r)^{1/r} ≤ C_r K^{1/r} (∑_{l < K} |B_l|^{r'})^{1/r'}`,

for `2 ≤ r < ∞`, `1/r + 1/r' = 1`, with `C_r` depending only on `r` (`C_2 = 1`), uniform in the
finite set `S ⊆ ℤ` and in `K`.

Difference from the printed statement: the classical inequalities have the sharp constant `1`
(Riesz–Thorin); here the constant is `C_r` (`hyConst r`), obtained by off-diagonal Marcinkiewicz
interpolation (`eLpNorm_le_interpolation_of_truncClosed`, vendored Carleson slice) between the
trivial `(1, ∞)` bound and Plancherel (`integral_norm_sq_sum_e`, from `integral_sum_mul_conj_sum`,
and `sum_norm_sq_cyclic`). Both uses only need `≲_r`: `e:embed` is stated with `≲_r` (L1106), the
endpoint step with `≲_r` (L1115), and the derivative step (L1109, printed `≲`, absolute) only feeds
the `≲_r` bound `e:embed`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Common

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-! ### `ℓ^p` and `L^p` norms as finite sums and integrals -/

section Norms

/-- The `ℓ^p` norm (`0 < p < ∞`) for counting measure of a function vanishing off a finite set. -/
theorem eLpNorm_count_eq_ofReal_sum {α G : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [NormedAddCommGroup G] {g : α → G}
    {S : Finset α} (hS : ∀ n ∉ S, g n = 0) {p : ℝ} (hp : 0 < p) :
    eLpNorm g (ENNReal.ofReal p) Measure.count =
      ENNReal.ofReal ((∑ n ∈ S, ‖g n‖ ^ p) ^ (1 / p)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top
    StronglyMeasurable.of_discrete.aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal hp.le,
    tsum_eq_sum (s := S) (fun n hn => by simp [hS n hn, ENNReal.zero_rpow_of_pos hp]),
    ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

/-- The `L^p` norm (`0 < p < ∞`) on `(0, 1]` of a continuous function, as an integral. -/
theorem eLpNorm_restrict_Ioc_eq_ofReal_integral {h : ℝ → ℂ} (hc : Continuous h) {p : ℝ}
    (hp : 0 < p) :
    eLpNorm h (ENNReal.ofReal p) (volume.restrict (Ioc (0 : ℝ) 1)) =
      ENNReal.ofReal ((∫ ξ in (0 : ℝ)..1, ‖h ξ‖ ^ p) ^ (1 / p)) := by
  have hint : IntegrableOn (fun ξ => ‖h ξ‖ ^ p) (Ioc (0 : ℝ) 1) volume :=
    (hc.norm.rpow_const fun _ => Or.inr hp.le).integrableOn_Ioc
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top
    hc.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le,
    intervalIntegral.integral_of_le zero_le_one,
    ← ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => by positivity) (by positivity),
    ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun ξ => by simp only [Pi.zero_apply]; positivity)]
  congr 1
  refine lintegral_congr fun ξ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

/-- The `ℓ¹` norm for counting measure is the sum of the norms. -/
theorem eLpNorm_one_count_eq_tsum {α G : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [TopologicalSpace G] [ContinuousENorm G]
    (g : α → G) : eLpNorm g 1 Measure.count = ∑' n, ‖g n‖ₑ := by
  rw [eLpNorm_one_eq_lintegral_enorm StronglyMeasurable.of_discrete.aestronglyMeasurable,
    lintegral_count]

end Norms

/-! ### Interpolation between the `(1, ∞)` bound and an `L²` bound -/

section OneTopTwoTwo

/-- The constant of the Hausdorff–Young inequalities obtained by interpolation: `1` for `r = 2`,
and the Marcinkiewicz constant for `(p₀, q₀) = (1, ∞)`, `(p₁, q₁) = (2, 2)`, `t = 2/r` otherwise.
It depends only on `r`. -/
def hyConst (r : ℝ) : ℝ≥0∞ :=
  if r = 2 then 1 else realInterpConst 1 2 ⊤ 2 (ENNReal.ofReal r) (ENNReal.ofReal (2 / r))

/-- The exponent relations of the `(1, ∞)`–`(2, 2)` interpolation at `t = 2/r`. -/
theorem hy_exponents {r r' : ℝ} (hr : 2 < r) (hrr' : r.HolderConjugate r') :
    (ENNReal.ofReal r')⁻¹ = (1 - ENNReal.ofReal (2 / r)) / 1 + ENNReal.ofReal (2 / r) / 2 ∧
      (ENNReal.ofReal r)⁻¹ = (1 - ENNReal.ofReal (2 / r)) / ⊤ + ENNReal.ofReal (2 / r) / 2 := by
  have hr0 : 0 < r := by linarith
  have h2r : 2 / r < 1 := (div_lt_one hr0).2 hr
  have hsum : r⁻¹ + r'⁻¹ = 1 := by simpa using hrr'.inv_add_inv_eq_inv
  have hhalf : ENNReal.ofReal (2 / r) / 2 = ENNReal.ofReal r⁻¹ := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_div_of_pos two_pos]
    congr 1
    field_simp
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_inv_of_pos hrr'.symm.pos, div_one, hhalf,
      one_sub_ofReal_eq (by positivity), ← ENNReal.ofReal_add (by linarith) (by positivity)]
    congr 1
    have : 2 / r = 2 * r⁻¹ := by ring
    rw [this]
    linarith
  · rw [ENNReal.div_top, zero_add, hhalf, ENNReal.ofReal_inv_of_pos hr0]

/-- `hyConst r` is finite for `2 ≤ r`. -/
theorem hyConst_ne_top {r : ℝ} (hr : 2 ≤ r) : hyConst r ≠ ⊤ := by
  unfold hyConst
  split_ifs with h
  · exact ENNReal.one_ne_top
  · have hr' : 2 < r := lt_of_le_of_ne hr (Ne.symm h)
    have hrr' : r.HolderConjugate (r / (r - 1)) :=
      Real.HolderConjugate.conjExponent (by linarith)
    exact realInterpConst_ne_top ⟨one_pos, le_top⟩ ⟨by norm_num, le_rfl⟩ (by simp)
      (ofReal_mem_Ioo_zero_one (by positivity) ((div_lt_one (by linarith)).2 hr'))
      (hy_exponents hr' hrr').2

variable {α β E₁ E₂ : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [TopologicalSpace E₁] [ESeminormedAddMonoid E₁] [TopologicalSpace E₂]
  [ESeminormedAddMonoid E₂]

/-- **Off-diagonal interpolation between `(1, ∞)` and `(2, 2)`.** If `T` is subadditive,
`‖T f‖_∞ ≤ ‖f‖₁` and `‖T f‖₂ ≤ M₁ ‖f‖₂`, then `‖T f‖_r ≤ C_r M₁^{2/r} ‖f‖_{r'}` for
`2 ≤ r < ∞`, `1/r + 1/r' = 1`, with `C_r = hyConst r`. -/
theorem eLpNorm_le_of_one_top_two_two {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r')
    {M₁ : ℝ≥0} (hM₁ : 0 < M₁) (T : (α → E₁) → β → E₂)
    (hmeas : ∀ f, AEStronglyMeasurable (T f) ν)
    (hsub : ∀ f g x, ‖T (f + g) x‖ₑ ≤ ‖T f x‖ₑ + ‖T g x‖ₑ)
    (h₀ : ∀ f, eLpNorm (T f) ⊤ ν ≤ eLpNorm f 1 μ)
    (h₁ : ∀ f, eLpNorm (T f) 2 ν ≤ M₁ * eLpNorm f 2 μ) (f : α → E₁) :
    eLpNorm (T f) (ENNReal.ofReal r) ν ≤
      hyConst r * (M₁ : ℝ≥0∞) ^ (2 / r) * eLpNorm f (ENNReal.ofReal r') μ := by
  rcases eq_or_lt_of_le hr with rfl | hr'
  · -- `r = 2 = r'`: the `L²` bound itself.
    have hr'2 : r' = 2 := by
      have hsum : (2 : ℝ)⁻¹ + r'⁻¹ = 1 := by simpa using hrr'.inv_add_inv_eq_inv
      have : r'⁻¹ = 2⁻¹ := by linarith
      simpa using this
    subst hr'2
    simp only [hyConst, ↓reduceIte, one_mul, div_self (two_ne_zero : (2 : ℝ) ≠ 0),
      ENNReal.rpow_one, ENNReal.ofReal_ofNat]
    exact h₁ f
  · obtain ⟨hp, hq⟩ := hy_exponents hr' hrr'
    have hr0 : 0 < r := by linarith
    have ht := ofReal_mem_Ioo_zero_one (by positivity : 0 < 2 / r) ((div_lt_one hr0).2 hr')
    have hP₀ : (1 : ℝ≥0∞) ∈ Ioc 0 ⊤ := ⟨one_pos, le_top⟩
    have hP₁ : (2 : ℝ≥0∞) ∈ Ioc 0 2 := ⟨by norm_num, le_rfl⟩
    have hq₀q₁ : (⊤ : ℝ≥0∞) ≠ 2 := by simp
    have hC : hyConst r = realInterpConst 1 2 ⊤ 2 (ENNReal.ofReal r) (ENNReal.ofReal (2 / r)) := by
      simp [hyConst, hr'.ne']
    rw [hC]
    by_cases hfp : MemLp f (ENNReal.ofReal r') μ
    · have key := eLpNorm_le_interpolation_of_truncClosed (μ := μ) (ν := ν)
        (fun _ : α → E₁ => True) (fun _ _ _ => trivial) (fun _ _ _ => trivial) hP₀ hP₁ hq₀q₁ ht
        hp hq one_pos hM₁ T (fun g _ => hmeas g)
        (fun g g' _ _ => ae_of_all _ (hsub g g'))
        (fun g _ _ => (wnorm_le_eLpNorm (hmeas g) (by simp)).trans (by simpa using h₀ g))
        (fun g _ _ => (wnorm_le_eLpNorm (hmeas g) (by norm_num)).trans (h₁ g)) trivial hfp
      rwa [ENNReal.coe_one, ENNReal.one_rpow, mul_one, ENNReal.toReal_ofReal (by positivity)]
        at key
    · rw [not_lt_top_iff.1 hfp, ENNReal.mul_top]
      · exact le_top
      · refine mul_ne_zero (realInterpConst_pos hP₀ hP₁ hq₀q₁ ht hq).ne' ?_
        exact (ENNReal.rpow_pos (by exact_mod_cast hM₁) ENNReal.coe_ne_top).ne'

end OneTopTwoTwo

/-! ### Hausdorff–Young on `𝕋` -/

section Torus

/-- The trigonometric polynomial `ξ ↦ ∑_{n ∈ S} g(n) e(nξ)`. -/
def trigSum (S : Finset ℤ) (g : ℤ → ℂ) (ξ : ℝ) : ℂ :=
  ∑ n ∈ S, g n * e ((n : ℝ) * ξ)

/-- A trigonometric polynomial is continuous. -/
theorem continuous_trigSum (S : Finset ℤ) (g : ℤ → ℂ) : Continuous (trigSum S g) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_e.comp (by fun_prop))

/-- Plancherel for `∑_{n ∈ S} g(n) e(nξ)`: `∫₀¹ |∑_{n ∈ S} g(n) e(nξ)|² = ∑_{n ∈ S} |g(n)|²`. -/
theorem integral_norm_sq_sum_e (S : Finset ℤ) (g : ℤ → ℂ) :
    ∫ ξ in (0 : ℝ)..1, ‖∑ n ∈ S, g n * e ((n : ℝ) * ξ)‖ ^ 2 = ∑ n ∈ S, ‖g n‖ ^ 2 := by
  have h := integral_sum_mul_conj_sum S (fun n => conj (g n)) (fun n => conj (g n)) 0
  rw [zero_add] at h
  have hP : ∀ ξ : ℝ, ∑ n ∈ S, conj (g n) * e (-((n : ℝ) * ξ)) =
      conj (∑ n ∈ S, g n * e ((n : ℝ) * ξ)) := by
    intro ξ
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, e_neg]
  simp only [hP, Complex.conj_conj] at h
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal, Complex.ofReal_sum]
  simp only [Complex.ofReal_pow, ← Complex.conj_mul']
  exact h

/-- The trivial bound `‖∑_{n ∈ S} g(n) e(n·)‖_∞ ≤ ‖g‖_{ℓ¹}`. -/
theorem eLpNorm_trigSum_top_le (S : Finset ℤ) (g : ℤ → ℂ) :
    eLpNorm (trigSum S g) ⊤ (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      eLpNorm g 1 Measure.count := by
  have hb : ∀ ξ, ‖trigSum S g ξ‖ₑ ≤ eLpNorm g 1 Measure.count := by
    intro ξ
    rw [eLpNorm_one_count_eq_tsum]
    calc ‖trigSum S g ξ‖ₑ ≤ ∑ n ∈ S, ‖g n * e ((n : ℝ) * ξ)‖ₑ := enorm_sum_le _ _
      _ = ∑ n ∈ S, ‖g n‖ₑ := Finset.sum_congr rfl fun n _ => by
          rw [enorm_mul, ← ofReal_norm (e _), norm_e, ENNReal.ofReal_one, mul_one]
      _ ≤ ∑' n, ‖g n‖ₑ := ENNReal.sum_le_tsum S
  exact (eLpNorm_le_of_ae_enorm_bound (continuous_trigSum S g).aestronglyMeasurable
    (ae_of_all _ hb)).trans (by simp)

/-- Plancherel as an `L²` bound: `‖∑_{n ∈ S} g(n) e(n·)‖_{L²(0,1)} ≤ ‖g‖_{ℓ²}`. -/
theorem eLpNorm_trigSum_two_le (S : Finset ℤ) (g : ℤ → ℂ) :
    eLpNorm (trigSum S g) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      eLpNorm g 2 Measure.count := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hS : ∀ n ∉ S, (↑S : Set ℤ).indicator g n = 0 := fun n hn =>
    Set.indicator_of_notMem (by simpa using hn) _
  calc eLpNorm (trigSum S g) 2 (volume.restrict (Ioc (0 : ℝ) 1))
      = eLpNorm ((↑S : Set ℤ).indicator g) 2 Measure.count := by
        rw [h2, eLpNorm_restrict_Ioc_eq_ofReal_integral (continuous_trigSum S g) two_pos,
          eLpNorm_count_eq_ofReal_sum hS two_pos]
        have hind : ∑ n ∈ S, ‖(↑S : Set ℤ).indicator g n‖ ^ 2 = ∑ n ∈ S, ‖g n‖ ^ 2 :=
          Finset.sum_congr rfl fun n hn => by rw [Set.indicator_of_mem (by simpa using hn)]
        simp only [Real.rpow_two, trigSum]
        rw [integral_norm_sq_sum_e, hind]
    _ ≤ eLpNorm g 2 Measure.count :=
        eLpNorm_indicator_le g (Finset.measurableSet S).nullMeasurableSet

/-- **Hausdorff–Young on `𝕋`, `L^p` form**: for `2 ≤ r < ∞`, `1/r + 1/r' = 1`, every finite
`S ⊆ ℤ` and `g : ℤ → ℂ`, `‖∑_{n ∈ S} g(n) e(n·)‖_{L^r(0,1)} ≤ C_r ‖g‖_{ℓ^{r'}}`. -/
theorem eLpNorm_trigSum_le {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r')
    (S : Finset ℤ) (g : ℤ → ℂ) :
    eLpNorm (trigSum S g) (ENNReal.ofReal r) (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      hyConst r * eLpNorm g (ENNReal.ofReal r') Measure.count := by
  have key := eLpNorm_le_of_one_top_two_two (μ := Measure.count)
    (ν := volume.restrict (Ioc (0 : ℝ) 1)) hr hrr' one_pos (trigSum S)
    (fun g => (continuous_trigSum S g).aestronglyMeasurable)
    (fun g g' ξ => by
      simp only [trigSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact enorm_add_le _ _)
    (eLpNorm_trigSum_top_le S) (fun g => by simpa using eLpNorm_trigSum_two_le S g) g
  simpa using key

/-- **Hausdorff–Young on `𝕋`** (with a constant `C_r` in place of `1`): for `2 ≤ r < ∞` and
`1/r + 1/r' = 1` there is `C` such that for every finite `S ⊆ ℤ` and `b : ℤ → ℂ`,
`(∫₀¹ |∑_{n ∈ S} b(n) e(nξ)|^r dξ)^{1/r} ≤ C (∑_{n ∈ S} |b(n)|^{r'})^{1/r'}`. -/
theorem hausdorffYoung_T {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℤ) (b : ℤ → ℂ),
      (∫ ξ in (0 : ℝ)..1, ‖∑ n ∈ S, b n * e ((n : ℝ) * ξ)‖ ^ r) ^ (1 / r) ≤
        C * (∑ n ∈ S, ‖b n‖ ^ r') ^ (1 / r') := by
  refine ⟨(hyConst r).toReal, ENNReal.toReal_nonneg, fun S b => ?_⟩
  have hr0 : 0 < r := by linarith
  have hS : ∀ n ∉ S, (↑S : Set ℤ).indicator b n = 0 := fun n hn =>
    Set.indicator_of_notMem (by simpa using hn) _
  have htrig : trigSum S ((↑S : Set ℤ).indicator b) = trigSum S b := by
    funext ξ
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Set.indicator_of_mem (by simpa using hn)]
  have key := eLpNorm_trigSum_le hr hrr' S ((↑S : Set ℤ).indicator b)
  rw [htrig, eLpNorm_restrict_Ioc_eq_ofReal_integral (continuous_trigSum S b) hr0,
    eLpNorm_count_eq_ofReal_sum hS hrr'.symm.pos,
    ← ENNReal.ofReal_toReal (hyConst_ne_top hr), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (by positivity))] at key
  have hsum : ∑ n ∈ S, ‖(↑S : Set ℤ).indicator b n‖ ^ r' = ∑ n ∈ S, ‖b n‖ ^ r' :=
    Finset.sum_congr rfl fun n hn => by rw [Set.indicator_of_mem (by simpa using hn)]
  rw [hsum] at key
  exact key

end Torus

/-! ### Hausdorff–Young on `ℤ / K` -/

section Cyclic

/-- The discrete Fourier sum `s ↦ ∑_{l < K} B(l) e(sl/K)` for `s < K`, extended by `0`. -/
def cyclicSum (K : ℕ) (B : ℕ → ℂ) (s : ℕ) : ℂ :=
  if s < K then ∑ l ∈ Finset.range K, B l * e ((s : ℝ) * l / K) else 0

/-- The trivial bound `‖∑_{l < K} B(l) e(·l/K)‖_∞ ≤ ‖B‖_{ℓ¹}`. -/
theorem eLpNorm_cyclicSum_top_le (K : ℕ) (B : ℕ → ℂ) :
    eLpNorm (cyclicSum K B) ⊤ Measure.count ≤ eLpNorm B 1 Measure.count := by
  have hb : ∀ s, ‖cyclicSum K B s‖ₑ ≤ eLpNorm B 1 Measure.count := by
    intro s
    rw [eLpNorm_one_count_eq_tsum]
    unfold cyclicSum
    split_ifs
    · calc ‖∑ l ∈ Finset.range K, B l * e ((s : ℝ) * l / K)‖ₑ
          ≤ ∑ l ∈ Finset.range K, ‖B l * e ((s : ℝ) * l / K)‖ₑ := enorm_sum_le _ _
        _ = ∑ l ∈ Finset.range K, ‖B l‖ₑ := Finset.sum_congr rfl fun l _ => by
            rw [enorm_mul, ← ofReal_norm (e _), norm_e, ENNReal.ofReal_one, mul_one]
        _ ≤ ∑' l, ‖B l‖ₑ := ENNReal.sum_le_tsum _
    · simp
  exact (eLpNorm_le_of_ae_enorm_bound StronglyMeasurable.of_discrete.aestronglyMeasurable
    (ae_of_all _ hb)).trans (by simp)

/-- Cyclic Plancherel as an `ℓ²` bound: `‖∑_{l < K} B(l) e(·l/K)‖_{ℓ²} ≤ K^{1/2} ‖B‖_{ℓ²}`. -/
theorem eLpNorm_cyclicSum_two_le {K : ℕ} (hK : 0 < K) (B : ℕ → ℂ) :
    eLpNorm (cyclicSum K B) 2 Measure.count ≤
      ENNReal.ofReal ((K : ℝ) ^ (1 / 2 : ℝ)) * eLpNorm B 2 Measure.count := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hT : ∀ s ∉ Finset.range K, cyclicSum K B s = 0 := fun s hs => by
    simp [cyclicSum, Finset.mem_range.not.1 hs]
  have hS : ∀ n ∉ Finset.range K, (↑(Finset.range K) : Set ℕ).indicator B n = 0 :=
    fun n hn => Set.indicator_of_notMem (by simpa using hn) _
  have hsum : ∑ s ∈ Finset.range K, ‖cyclicSum K B s‖ ^ 2 =
      K * ∑ l ∈ Finset.range K, ‖(↑(Finset.range K) : Set ℕ).indicator B l‖ ^ 2 := by
    have hind : ∑ l ∈ Finset.range K, ‖(↑(Finset.range K) : Set ℕ).indicator B l‖ ^ 2 =
        ∑ l ∈ Finset.range K, ‖B l‖ ^ 2 :=
      Finset.sum_congr rfl fun l hl => by rw [Set.indicator_of_mem (by simpa using hl)]
    rw [hind, ← sum_norm_sq_cyclic hK B]
    exact Finset.sum_congr rfl fun s hs => by
      simp only [cyclicSum, Finset.mem_range.1 hs, ↓reduceIte]
  calc eLpNorm (cyclicSum K B) 2 Measure.count
      = ENNReal.ofReal ((K : ℝ) ^ (1 / 2 : ℝ)) *
          eLpNorm ((↑(Finset.range K) : Set ℕ).indicator B) 2 Measure.count := by
        rw [h2, eLpNorm_count_eq_ofReal_sum hT two_pos, eLpNorm_count_eq_ofReal_sum hS two_pos,
          ← ENNReal.ofReal_mul (by positivity)]
        simp only [Real.rpow_two]
        rw [hsum, Real.mul_rpow (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)]
    _ ≤ ENNReal.ofReal ((K : ℝ) ^ (1 / 2 : ℝ)) * eLpNorm B 2 Measure.count := by
        gcongr
        exact eLpNorm_indicator_le B (Finset.measurableSet _).nullMeasurableSet

/-- **Discrete Hausdorff–Young on `ℤ / K`, `ℓ^p` form**: for `2 ≤ r < ∞`, `1/r + 1/r' = 1`,
`‖∑_{l < K} B(l) e(·l/K)‖_{ℓ^r} ≤ C_r K^{1/r} ‖B‖_{ℓ^{r'}}`. -/
theorem eLpNorm_cyclicSum_le {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') {K : ℕ}
    (hK : 0 < K) (B : ℕ → ℂ) :
    eLpNorm (cyclicSum K B) (ENNReal.ofReal r) Measure.count ≤
      hyConst r * ENNReal.ofReal ((K : ℝ) ^ (1 / r)) *
        eLpNorm B (ENNReal.ofReal r') Measure.count := by
  have hr0 : 0 < r := by linarith
  have hM : 0 < Real.toNNReal ((K : ℝ) ^ (1 / 2 : ℝ)) :=
    Real.toNNReal_pos.2 (Real.rpow_pos_of_pos (by exact_mod_cast hK) _)
  have key := eLpNorm_le_of_one_top_two_two (μ := Measure.count) (ν := Measure.count) hr hrr'
    hM (cyclicSum K) (fun _ => StronglyMeasurable.of_discrete.aestronglyMeasurable)
    (fun g g' s => by
      unfold cyclicSum
      split_ifs
      · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        exact enorm_add_le _ _
      · simp)
    (eLpNorm_cyclicSum_top_le K) (eLpNorm_cyclicSum_two_le hK) B
  have hpow : ((Real.toNNReal ((K : ℝ) ^ (1 / 2 : ℝ)) : ℝ≥0∞)) ^ (2 / r) =
      ENNReal.ofReal ((K : ℝ) ^ (1 / r)) := by
    rw [show ((Real.toNNReal ((K : ℝ) ^ (1 / 2 : ℝ)) : ℝ≥0∞)) =
        ENNReal.ofReal ((K : ℝ) ^ (1 / 2 : ℝ)) from rfl,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity)]
    congr 2
    field_simp
  rwa [hpow] at key

/-- **Discrete Hausdorff–Young on `ℤ / K`** (with a constant `C_r` in place of `1`): for `2 ≤ r < ∞`
and `1/r + 1/r' = 1` there is `C` such that for every `K` and `B : ℕ → ℂ`,
`(∑_{s < K} |∑_{l < K} B(l) e(sl/K)|^r)^{1/r} ≤ C K^{1/r} (∑_{l < K} |B(l)|^{r'})^{1/r'}`. -/
theorem hausdorffYoung_cyclic {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℕ) (B : ℕ → ℂ),
      (∑ s ∈ Finset.range K, ‖∑ l ∈ Finset.range K, B l * e ((s : ℝ) * l / K)‖ ^ r) ^ (1 / r)
        ≤ C * (K : ℝ) ^ (1 / r) * (∑ l ∈ Finset.range K, ‖B l‖ ^ r') ^ (1 / r') := by
  refine ⟨(hyConst r).toReal, ENNReal.toReal_nonneg, fun K B => ?_⟩
  have hr0 : 0 < r := by linarith
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [Real.zero_rpow, hr0.ne', hrr'.symm.pos.ne']
  have hT : ∀ s ∉ Finset.range K, cyclicSum K ((↑(Finset.range K) : Set ℕ).indicator B) s = 0 :=
    fun s hs => by simp [cyclicSum, Finset.mem_range.not.1 hs]
  have hS : ∀ n ∉ Finset.range K, (↑(Finset.range K) : Set ℕ).indicator B n = 0 :=
    fun n hn => Set.indicator_of_notMem (by simpa using hn) _
  have key := eLpNorm_cyclicSum_le hr hrr' hK ((↑(Finset.range K) : Set ℕ).indicator B)
  rw [eLpNorm_count_eq_ofReal_sum hT hr0, eLpNorm_count_eq_ofReal_sum hS hrr'.symm.pos,
    ← ENNReal.ofReal_toReal (hyConst_ne_top hr), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have h1 : ∑ s ∈ Finset.range K, ‖cyclicSum K ((↑(Finset.range K) : Set ℕ).indicator B) s‖ ^ r
      = ∑ s ∈ Finset.range K, ‖∑ l ∈ Finset.range K, B l * e ((s : ℝ) * l / K)‖ ^ r := by
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [cyclicSum, Finset.mem_range.1 hs, ↓reduceIte]
    congr 2
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Set.indicator_of_mem (by simpa using hl)]
  have h2 : ∑ l ∈ Finset.range K, ‖(↑(Finset.range K) : Set ℕ).indicator B l‖ ^ r' =
      ∑ l ∈ Finset.range K, ‖B l‖ ^ r' :=
    Finset.sum_congr rfl fun l hl => by rw [Set.indicator_of_mem (by simpa using hl)]
  rw [h1, h2] at key
  exact key

end Cyclic

end PrimeCarleson.Proof.Common
