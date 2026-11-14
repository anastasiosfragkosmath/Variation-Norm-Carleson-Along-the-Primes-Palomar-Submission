module

public import PrimeCarleson.Proof.Oplus.TilesLarge.Sparsity
public import PrimeCarleson.Proof.Oplus.Estimates.All

/-!
# The coefficient bounds at one time interval ([O+] L2487-L2525)

[O+] L2487-L2525 (the `ℓ²`, `sup` and `ℓ^r` coefficient bounds in the proof of `tileslargemaxprop`):
for a dyadic interval `I_ℓ` with `2^{ℓ+1} I_ℓ ⊄ Ω_λ`,
`Ω_λ = {M[1_F] > λ}` (`maxSuperlevel`), `|f| ≤ 1_F`, and the `ρ`-multitiles `P` with `I = I_ℓ`:

* `ℓ²`: `(∑_{P : I = I_ℓ} |⟨f, φ_P⟩|²)^{1/2} ≲ (2^ℓ λ |I_ℓ|)^{1/2}`
  (`exists_sqrt_sum_norm_sq_coeff_le`);
* `ℓ^∞`: `sup_{P : I = I_ℓ} |⟨f, φ_P⟩| ≲ 2^ℓ λ |I_ℓ|^{1/2}` (`exists_norm_coeff_le_sup`);
* `ℓ^r`, `2 ≤ r < ∞`: `(∑_{P : I = I_ℓ} |⟨f, φ_P⟩|^r)^{1/r} ≲ (2^ℓ λ)^{1/r'} |I_ℓ|^{1/2}`
  (`exists_rpow_sum_norm_coeff_le`), with one constant for all `r`.

The `ℓ²` bound is the source's: `f = 1_{4 I_ℓ} f + ∑_j 1_{2^{j+1} I_ℓ ∖ 2^j I_ℓ} f` (the annuli
`Dyadic.annulus`, a partition of `ℝ` into `2 I`, `4 I ∖ 2 I`, `8 I ∖ 4 I`, …), the same-interval
orthogonality of `Estimates/SameInterval.lean` on each annulus (`Multitile.sum_norm_sq_coeff_le`),
the packet bound `wavepacketadaptedbound` and the sparsity of `F` of `Sparsity.lean`; the
(countable) triangle inequality in `ℓ²` is `sqrt_sum_norm_sq_le_tsum`. The `ℓ^∞` bound is
`|⟨f, φ_P⟩| ≤ ∫_F |φ_P|` with the weighted mass of `F` of `Sparsity.lean`. The interpolation of
the source ("by interpolation") is the elementary `∑ |c|^r ≤ (sup |c|)^{r-2} ∑ |c|²`
(`sum_rpow_le_of_sup_le_of_sum_sq_le`). The constants depend on `N` only (not on `ρ`, the
profile choice, `r`, `F`, `f`, `λ`, `ℓ`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### The triangle inequality in `ℓ²` for countable sums -/

/-- The triangle inequality in `ℓ²(s)` for two vectors. -/
theorem sqrt_sum_norm_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ) :
    √(∑ i ∈ s, ‖x i + y i‖ ^ 2) ≤ √(∑ i ∈ s, ‖x i‖ ^ 2) + √(∑ i ∈ s, ‖y i‖ ^ 2) := by
  set A := ∑ i ∈ s, ‖x i‖ ^ 2 with hA
  set B := ∑ i ∈ s, ‖y i‖ ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => by positivity
  have hcs : ∑ i ∈ s, ‖x i‖ * ‖y i‖ ≤ √A * √B :=
    Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖x i‖) (fun i => ‖y i‖)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ i ∈ s, ‖x i + y i‖ ^ 2 ≤ ∑ i ∈ s, (‖x i‖ ^ 2 + 2 * (‖x i‖ * ‖y i‖) + ‖y i‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_add_le (x i) (y i)
        have h2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        linarith only [h2]
    _ = A + 2 * ∑ i ∈ s, ‖x i‖ * ‖y i‖ + B := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ A + 2 * (√A * √B) + B := by linarith
    _ = (√A + √B) ^ 2 := by
        linarith [Real.sq_sqrt hA0, Real.sq_sqrt hB0]

/-- The triangle inequality in `ℓ²(s)` for a finite sum of vectors. -/
theorem sqrt_sum_norm_sq_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (v : κ → ι → ℂ) :
    √(∑ i ∈ s, ‖∑ k ∈ t, v k i‖ ^ 2) ≤ ∑ k ∈ t, √(∑ i ∈ s, ‖v k i‖ ^ 2) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (sqrt_sum_norm_sq_add_le s (v a) (fun i => ∑ k ∈ t, v k i)).trans (by linarith)

/-- The triangle inequality in `ℓ²(s)` for a series: if `c i = ∑' n, v n i` for `i ∈ s` and
`‖v n‖_{ℓ²(s)} ≤ a n` with `a` summable then `‖c‖_{ℓ²(s)} ≤ ∑' n, a n`. -/
theorem sqrt_sum_norm_sq_le_tsum {ι : Type*} (s : Finset ι) (v : ℕ → ι → ℂ) (c : ι → ℂ)
    (a : ℕ → ℝ) (ha : Summable a) (hv : ∀ i ∈ s, HasSum (fun n => v n i) (c i))
    (hva : ∀ n, √(∑ i ∈ s, ‖v n i‖ ^ 2) ≤ a n) :
    √(∑ i ∈ s, ‖c i‖ ^ 2) ≤ ∑' n, a n := by
  have ha0 : ∀ n, 0 ≤ a n := fun n => (Real.sqrt_nonneg _).trans (hva n)
  have hlim : Tendsto (fun M : ℕ => √(∑ i ∈ s, ‖∑ n ∈ Finset.range M, v n i‖ ^ 2)) atTop
      (𝓝 (√(∑ i ∈ s, ‖c i‖ ^ 2))) := by
    refine (Real.continuous_sqrt.tendsto _).comp ?_
    refine tendsto_finsetSum _ fun i hi => ?_
    exact ((hv i hi).tendsto_sum_nat).norm.pow 2
  refine le_of_tendsto hlim (Eventually.of_forall fun M => ?_)
  calc √(∑ i ∈ s, ‖∑ n ∈ Finset.range M, v n i‖ ^ 2)
      ≤ ∑ n ∈ Finset.range M, √(∑ i ∈ s, ‖v n i‖ ^ 2) := sqrt_sum_norm_sq_sum_le s _ v
    _ ≤ ∑ n ∈ Finset.range M, a n := Finset.sum_le_sum fun n _ => hva n
    _ ≤ ∑' n, a n := ha.sum_le_tsum _ (fun n _ => ha0 n)

/-! ### The annuli around a dyadic interval -/

/-- The annuli `B_0 = 2 I`, `B_{n+1} = 2^{n+2} I ∖ 2^{n+1} I` (the sets `1_{4 I_ℓ}`-and-
`1_{2^{j+1} I_ℓ ∖ 2^j I_ℓ}` of L2491-L2499, with the dilate `2 I` as the innermost piece), a
partition of `ℝ`. -/
def Dyadic.annulus (I : Dyadic) : ℕ → Set ℝ :=
  disjointed fun n : ℕ => I.dilate ((2 : ℝ) ^ (n + 1))

/-- The dilates `2^{n+1} I` exhaust `ℝ`. -/
theorem Dyadic.iUnion_dilate_pow (I : Dyadic) :
    ⋃ n : ℕ, I.dilate ((2 : ℝ) ^ (n + 1)) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  have hL := I.length_pos
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (|x - I.center| / I.length) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_⟩
  rw [Dyadic.dilate_two_pow_succ]
  have h1 : |x - I.center| < 2 ^ n * I.length := by
    rwa [div_lt_iff₀ hL] at hn
  rw [abs_lt] at h1
  constructor <;> linarith [h1.1, h1.2]

/-- The annuli cover `ℝ`. -/
theorem Dyadic.iUnion_annulus (I : Dyadic) : ⋃ n, I.annulus n = univ := by
  unfold Dyadic.annulus
  rw [iUnion_disjointed, I.iUnion_dilate_pow]

/-- The annuli are pairwise disjoint. -/
theorem Dyadic.pairwise_disjoint_annulus (I : Dyadic) :
    Pairwise (Function.onFun Disjoint I.annulus) :=
  disjoint_disjointed _

/-- The annuli are measurable. -/
theorem Dyadic.measurableSet_annulus (I : Dyadic) (n : ℕ) : MeasurableSet (I.annulus n) :=
  MeasurableSet.disjointed (fun _ => measurableSet_Ico) n

/-- `B_n ⊆ 2^{n+1} I`. -/
theorem Dyadic.annulus_subset (I : Dyadic) (n : ℕ) :
    I.annulus n ⊆ I.dilate ((2 : ℝ) ^ (n + 1)) :=
  disjointed_subset _ n

/-- On the annulus `B_n`: `2^n / 2 ≤ 1 + |x - c(I)|/|I|`. -/
theorem Dyadic.half_pow_le_of_mem_annulus {I : Dyadic} {n : ℕ} {x : ℝ} (hx : x ∈ I.annulus n) :
    (2 : ℝ) ^ n / 2 ≤ 1 + |x - I.center| / I.length := by
  have hL := I.length_pos
  have h0 : 0 ≤ |x - I.center| / I.length := by positivity
  cases n with
  | zero => norm_num; linarith
  | succ m =>
    have hx' : x ∈ I.annulus (m + 1) := hx
    unfold Dyadic.annulus at hx'
    rw [disjointed_eq_inter_compl] at hx'
    have hnot : x ∉ I.dilate ((2 : ℝ) ^ (m + 1)) := by
      have := (mem_iInter₂.1 hx'.2) m (Nat.lt_succ_self m)
      simpa using this
    have h1 : 2 ^ m * I.length ≤ |x - I.center| := by
      by_contra hlt
      rw [not_le] at hlt
      apply hnot
      rw [Dyadic.dilate_two_pow_succ]
      rw [abs_lt] at hlt
      constructor <;> linarith [hlt.1, hlt.2]
    have h2 : (2 : ℝ) ^ m ≤ |x - I.center| / I.length := by
      rw [le_div_iff₀ hL]; exact h1
    have : (2 : ℝ) ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ]; ring
    rw [this]; linarith

/-! ### The `ℓ^∞` bound -/

/-- **`tileslargemaxprop`** ([O+] L2517-L2520): there is `K` such that for
every `ρ`-multitile `P`, profile choice, measurable `F`, `f` with `|f| ≤ 1_F` and `λ ≥ 0`, if
`2^{ℓ+1} I ⊄ Ω_λ` for the time interval `I` of `P` then
`|⟨f, φ_P⟩| ≤ K 2^ℓ λ |I|^{1/2}`. -/
theorem exists_norm_coeff_le_sup :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} (ch : ProfileChoice) (P : Multitile ρ) {F : Set ℝ} {f : ℝ → ℂ},
      MeasurableSet F → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {lam : ℝ}, 0 ≤ lam →
      ∀ {ℓ : ℕ}, ¬ P.I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam →
        ‖P.coeff ch f‖ ≤ K * (2 ^ ℓ * lam) * √P.I.length := by
  obtain ⟨A, hA0, hA⟩ := Multitile.exists_norm_wavePacket_le 2
  refine ⟨16 * A, by positivity, ?_⟩
  intro ρ ch P F f hF hf lam hlam ℓ h
  have hL := P.I.length_pos
  set w : ℝ → ℝ := fun y => (1 + |y - P.I.center| / P.I.length) ^ (-2 : ℤ) with hw
  have hwint : Integrable w := by
    have := integrable_one_add_abs_div_zpow (N := 2) le_rfl P.I.center hL
    have h22 : (-((2 : ℕ) : ℤ)) = -2 := by norm_num
    rw [h22] at this
    exact this
  set B : ℝ → ℝ := F.indicator (fun y => A * (√P.I.length)⁻¹ * w y) with hB
  have hBint : Integrable B := (hwint.const_mul _).indicator hF
  have hpt : ∀ᵐ x, ‖f x * (starRingEnd ℂ) (P.wavePacket ch x)‖ ≤ B x := by
    filter_upwards [hf] with x hx
    rw [norm_mul, Complex.norm_conj]
    by_cases hxF : x ∈ F
    · rw [hB, Set.indicator_of_mem hxF]
      rw [Set.indicator_of_mem hxF] at hx
      have hφ := hA ρ ch P x
      have h2 : (-((2 : ℕ) : ℤ)) = -2 := by norm_num
      rw [h2] at hφ
      calc ‖f x‖ * ‖P.wavePacket ch x‖ ≤ 1 * (A * (√P.I.length)⁻¹ * w x) :=
            mul_le_mul hx hφ (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [hB, Set.indicator_of_notMem hxF]
      rw [Set.indicator_of_notMem hxF] at hx
      have : ‖f x‖ = 0 := le_antisymm hx (norm_nonneg _)
      rw [this, zero_mul]
  have h1 : ‖P.coeff ch f‖ ≤ ∫ x, B x := by
    unfold Multitile.coeff pairing
    exact norm_integral_le_of_norm_le hBint hpt
  have h2 : ∫ x, B x = A * (√P.I.length)⁻¹ * ∫ y in F, w y := by
    rw [hB, integral_indicator hF, integral_const_mul]
  have h3 := integral_weight_inter_le_of_not_subset hF hlam h
  have hs : √P.I.length * √P.I.length = P.I.length := Real.mul_self_sqrt hL.le
  have hs0 : 0 < √P.I.length := Real.sqrt_pos.2 hL
  rw [h2] at h1
  refine h1.trans ?_
  calc A * (√P.I.length)⁻¹ * ∫ y in F, w y
      ≤ A * (√P.I.length)⁻¹ * (16 * (2 ^ ℓ * lam) * P.I.length) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 16 * A * (2 ^ ℓ * lam) * ((√P.I.length)⁻¹ * P.I.length) := by ring
    _ = 16 * A * (2 ^ ℓ * lam) * √P.I.length := by
        have e : (√P.I.length)⁻¹ * P.I.length = √P.I.length := by
          rw [inv_mul_eq_div, div_eq_iff hs0.ne']; exact hs.symm
        rw [e]

/-! ### The `ℓ²` bound -/

/-- The `ℓ²` bound for the coefficients of one annulus piece `1_{B_n} f`: for the
`ρ`-multitiles `S` with a common time interval `I₀` (so `2^{ℓ+1} I₀ ⊄ Ω_λ`),
`(∑_{P ∈ S} |⟨1_{B_n} f, φ_P⟩|²)^{1/2} ≤ K 2^{-n} (2^ℓ λ |I₀|)^{1/2}` (same-interval orthogonality
on the annulus, the packet bound with decay `N` and the sparsity of `F`). -/
theorem exists_sqrt_sum_norm_sq_coeff_annulus_le (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} (ch : ProfileChoice) (S : Finset (Multitile ρ)) {I₀ : Dyadic},
      (∀ P ∈ S, P.I = I₀) → ∀ {F : Set ℝ} {f : ℝ → ℂ}, MeasurableSet F →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      ∀ {lam : ℝ}, 0 ≤ lam → ∀ {ℓ : ℕ}, ¬ I₀.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam →
      ∀ n : ℕ, √(∑ P ∈ S, ‖P.coeff ch ((I₀.annulus n).indicator f)‖ ^ 2) ≤
        K * (1 / 2) ^ n * √(2 ^ ℓ * lam * I₀.length) := by
  obtain ⟨A, hA0, hA⟩ := Multitile.exists_norm_wavePacket_le N
  refine ⟨3 * A * 2 ^ N, by positivity, ?_⟩
  intro ρ ch S I₀ hS F f hF hfm hfF lam hlam ℓ h n
  rcases S.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩
  · simp only [Finset.sum_empty, Real.sqrt_zero]
    positivity
  have hP₀I : P₀.I = I₀ := hS P₀ hP₀
  have hL := I₀.length_pos
  set L := I₀.length with hLdef
  set B := I₀.annulus n with hBdef
  have hBm : MeasurableSet B := I₀.measurableSet_annulus n
  set g : ℝ → ℂ := B.indicator f with hg
  have hgm : AEStronglyMeasurable g volume := hfm.indicator hBm
  have hgb : ∀ᵐ x, ‖g x‖ ≤ (F ∩ B).indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hfF] with x hx
    by_cases hxB : x ∈ B
    · rw [hg, Set.indicator_of_mem hxB]
      by_cases hxF : x ∈ F
      · have hxm : x ∈ F ∩ B := ⟨hxF, hxB⟩
        rw [Set.indicator_of_mem hxm]
        rw [Set.indicator_of_mem hxF] at hx
        exact hx
      · rw [Set.indicator_of_notMem (fun h' : x ∈ F ∩ B => hxF h'.1)]
        rw [Set.indicator_of_notMem hxF] at hx
        exact hx
    · rw [hg, Set.indicator_of_notMem hxB]
      simp [Set.indicator_nonneg]
  have hgb1 : ∀ᵐ x, ‖g x‖ ≤ 1 := by
    filter_upwards [hgb] with x hx
    refine hx.trans ?_
    by_cases hxm : x ∈ F ∩ B
    · simp [hxm]
    · simp [hxm]
  have hgsupp : Function.support g ⊆ I₀.dilate ((2 : ℝ) ^ (n + 1)) :=
    (Set.support_indicator_subset).trans (I₀.annulus_subset n)
  have hgmem : MemLp g 2 volume := memLp_two_of_bounded_of_support_subset_dilate hgm hgb1 hgsupp
  have hC : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have horth := Multitile.sqrt_sum_norm_sq_coeff_le ch S hS hP₀I hC hgmem hgsupp
  -- the packet bound on the annulus
  set t : ℝ := 2 ^ n with ht
  have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith
  set E : ℝ := (((2 : ℝ) ^ n / 2) ^ N)⁻¹ with hE
  set c : ℝ := A ^ 2 * L⁻¹ * E ^ 2 with hc
  have hE0 : 0 < E := by positivity
  have hφ : ∀ x ∈ B, ‖P₀.wavePacket ch x‖ ^ 2 ≤ c := by
    intro x hx
    have h1 := hA ρ ch P₀ x
    rw [hP₀I] at h1
    have h2 : (1 + |x - I₀.center| / L) ^ (-(N : ℤ)) ≤ E := by
      rw [zpow_neg, zpow_natCast, hE]
      have := I₀.half_pow_le_of_mem_annulus hx
      refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) this N)
    have h3 : ‖P₀.wavePacket ch x‖ ≤ A * (√L)⁻¹ * E := h1.trans (by gcongr)
    have h4 : (A * (√L)⁻¹ * E) ^ 2 = c := by
      rw [hc, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hL.le]
    rw [← h4]
    exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  -- the integral
  have hvol : volume (F ∩ B) ≤ ENNReal.ofReal (2 * lam * 2 ^ (max ℓ n) * L) :=
    (measure_mono (inter_subset_inter_right _ (I₀.annulus_subset n))).trans
      (volume_inter_dilate_le_of_not_subset hF hlam h n)
  have hfin : volume (F ∩ B) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have hV : volume.real (F ∩ B) ≤ 2 * lam * (2 ^ ℓ * t) * L := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    refine h1.trans ?_
    have := two_pow_max_le ℓ n
    have h3 : 0 ≤ 2 * lam * L := by positivity
    linarith [mul_le_mul_of_nonneg_left this h3]
  have hJ : ∫ x, ‖g x‖ ^ 2 * ‖P₀.wavePacket ch x‖ ^ 2 ≤ c * volume.real (F ∩ B) := by
    have hind : Integrable ((F ∩ B).indicator (fun _ => c)) :=
      (integrable_indicator_iff (hF.inter hBm)).2 (integrableOn_const hfin)
    calc ∫ x, ‖g x‖ ^ 2 * ‖P₀.wavePacket ch x‖ ^ 2
        ≤ ∫ x, (F ∩ B).indicator (fun _ => c) x := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hind ?_
          filter_upwards [hgb] with x hx
          by_cases hxm : x ∈ F ∩ B
          · rw [Set.indicator_of_mem hxm]
            rw [Set.indicator_of_mem hxm] at hx
            have h1 : ‖g x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hx
            calc ‖g x‖ ^ 2 * ‖P₀.wavePacket ch x‖ ^ 2 ≤ 1 * c :=
                  mul_le_mul h1 (hφ x hxm.2) (by positivity) zero_le_one
              _ = c := one_mul c
          · rw [Set.indicator_of_notMem hxm]
            rw [Set.indicator_of_notMem hxm] at hx
            have : ‖g x‖ = 0 := le_antisymm hx (norm_nonneg _)
            rw [this]; simp
      _ = c * volume.real (F ∩ B) := by
          rw [integral_indicator_const _ (hF.inter hBm), smul_eq_mul, mul_comm]
  -- the algebra
  set u : ℝ := 2 ^ ℓ * lam * L with hu
  have hu0 : 0 ≤ u := by positivity
  have hEt : E ≤ 2 ^ N / t ^ 2 := by
    rw [hE, div_pow, inv_div]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact pow_le_pow_right₀ ht1 hN
  have key : (2 * 2 ^ (n + 1) * L) * (c * volume.real (F ∩ B)) ≤
      (3 * A * 2 ^ N * (1 / 2) ^ n) ^ 2 * u := by
    have e1 : (1 / 2 : ℝ) ^ n = t⁻¹ := by rw [one_div, inv_pow]
    have e2 : (2 : ℝ) ^ (n + 1) = 2 * t := by rw [pow_succ, ht]; ring
    rw [e1, e2]
    have hc0 : 0 ≤ c := by positivity
    calc (2 * (2 * t) * L) * (c * volume.real (F ∩ B))
        ≤ (2 * (2 * t) * L) * (c * (2 * lam * (2 ^ ℓ * t) * L)) := by gcongr
      _ = 8 * A ^ 2 * t ^ 2 * E ^ 2 * u := by
          rw [hc, hu]; field_simp; ring
      _ ≤ 8 * A ^ 2 * t ^ 2 * (2 ^ N / t ^ 2) ^ 2 * u := by gcongr
      _ = 8 * (A ^ 2 * 2 ^ (2 * N) * (t⁻¹) ^ 2 * u) := by
          rw [pow_mul']; field_simp
      _ ≤ 9 * (A ^ 2 * 2 ^ (2 * N) * (t⁻¹) ^ 2 * u) := by
          have : 0 ≤ A ^ 2 * 2 ^ (2 * N) * (t⁻¹) ^ 2 * u := by positivity
          linarith
      _ = (3 * A * 2 ^ N * t⁻¹) ^ 2 * u := by
          rw [pow_mul']; ring
  calc √(∑ P ∈ S, ‖P.coeff ch g‖ ^ 2)
      ≤ √(2 * 2 ^ (n + 1) * L) * √(∫ x, ‖g x‖ ^ 2 * ‖P₀.wavePacket ch x‖ ^ 2) := horth
    _ ≤ √(2 * 2 ^ (n + 1) * L) * √(c * volume.real (F ∩ B)) := by
        gcongr
    _ = √((2 * 2 ^ (n + 1) * L) * (c * volume.real (F ∩ B))) := by
        rw [← Real.sqrt_mul (by positivity)]
    _ ≤ √((3 * A * 2 ^ N * (1 / 2) ^ n) ^ 2 * u) := Real.sqrt_le_sqrt key
    _ = 3 * A * 2 ^ N * (1 / 2) ^ n * √u := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ = 3 * A * 2 ^ N * (1 / 2) ^ n * √(2 ^ ℓ * lam * L) := rfl

/-- **`tileslargemaxprop`** ([O+] L2487-L2516): there is `K`, depending only
on `N ≥ 2`, such that for every `ρ` (any index), profile choice, finite set `S` of `ρ`-multitiles
with a common time interval `I₀`, measurable `F`, `f` with `|f| ≤ 1_F`, `λ ≥ 0` and `ℓ` with
`2^{ℓ+1} I₀ ⊄ Ω_λ`,
`(∑_{P ∈ S} |⟨f, φ_P⟩|²)^{1/2} ≤ K (2^ℓ λ |I₀|)^{1/2}`. -/
theorem exists_sqrt_sum_norm_sq_coeff_le (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} (ch : ProfileChoice) (S : Finset (Multitile ρ)) {I₀ : Dyadic},
      (∀ P ∈ S, P.I = I₀) → ∀ {F : Set ℝ} {f : ℝ → ℂ}, MeasurableSet F →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      ∀ {lam : ℝ}, 0 ≤ lam → ∀ {ℓ : ℕ}, ¬ I₀.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam →
        √(∑ P ∈ S, ‖P.coeff ch f‖ ^ 2) ≤ K * √(2 ^ ℓ * lam * I₀.length) := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_sqrt_sum_norm_sq_coeff_annulus_le N hN
  refine ⟨2 * K₀, by positivity, ?_⟩
  intro ρ ch S I₀ hS F f hF hfm hfF lam hlam ℓ h
  set u : ℝ := √(2 ^ ℓ * lam * I₀.length) with hu
  have hsum : Summable (fun n : ℕ => K₀ * (1 / 2) ^ n * u) :=
    (summable_geometric_two.mul_left K₀).mul_right u
  have hfb : ∀ᵐ x, ‖f x‖ ≤ 1 := by
    filter_upwards [hfF] with x hx
    refine hx.trans ?_
    by_cases hxF : x ∈ F <;> simp [hxF]
  have hHas : ∀ P ∈ S,
      HasSum (fun n => P.coeff ch ((I₀.annulus n).indicator f)) (P.coeff ch f) := by
    intro P _
    have hint : Integrable (fun x => f x * (starRingEnd ℂ) (P.wavePacket ch x)) :=
      integrable_mul_conj_wavePacketOf_of_bdd ch.isProfile hfm hfb P.I P.ωu
    have h1 := hasSum_integral_iUnion (μ := volume) (fun n => I₀.measurableSet_annulus n)
      I₀.pairwise_disjoint_annulus hint.integrableOn
    rw [I₀.iUnion_annulus, Measure.restrict_univ] at h1
    convert h1 using 1
    · funext n
      unfold Multitile.coeff pairing
      rw [← integral_indicator (I₀.measurableSet_annulus n)]
      congr 1
      funext x
      by_cases hx : x ∈ I₀.annulus n <;> simp [hx]
    · rfl
  have hmain := sqrt_sum_norm_sq_le_tsum S
    (fun n P => P.coeff ch ((I₀.annulus n).indicator f)) (fun P => P.coeff ch f) _ hsum hHas
    (fun n => hK ch S hS hF hfm hfF hlam h n)
  refine hmain.trans (le_of_eq ?_)
  rw [tsum_mul_right, tsum_mul_left, tsum_geometric_two]
  ring

/-! ### The `ℓ^r` bound -/

/-- The elementary interpolation between `ℓ²` and `ℓ^∞`:
`∑ c_i^r ≤ M^{r-2} ∑ c_i²` for `0 ≤ c_i ≤ M` and `r ≥ 2`. -/
theorem sum_rpow_le_of_sup_le_of_sum_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) {M A r : ℝ}
    (hr : 2 ≤ r) (hc0 : ∀ i ∈ s, 0 ≤ c i) (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, c i ≤ M)
    (hA : ∑ i ∈ s, c i ^ 2 ≤ A) : ∑ i ∈ s, c i ^ r ≤ M ^ (r - 2) * A := by
  have hr0 : 0 < r := by linarith
  calc ∑ i ∈ s, c i ^ r ≤ ∑ i ∈ s, M ^ (r - 2) * c i ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        rcases (hc0 i hi).eq_or_lt with h0 | hpos
        · rw [← h0, Real.zero_rpow hr0.ne']
          positivity
        · have e : c i ^ r = c i ^ (r - 2) * c i ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
            norm_num
          rw [e]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (hc0 i hi) (hM i hi) (by linarith)) (by positivity)
    _ = M ^ (r - 2) * ∑ i ∈ s, c i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ M ^ (r - 2) * A := mul_le_mul_of_nonneg_left hA (by positivity)

/-- `1/r' = 1 - 1/r` for the conjugate exponent `r' = r/(r-1)`. -/
theorem one_div_conjExponent_eq {r : ℝ} (hr : 1 < r) :
    1 / Real.conjExponent r = 1 - 1 / r := by
  have h1 : r - 1 ≠ 0 := by linarith
  have h2 : r ≠ 0 := by linarith
  unfold Real.conjExponent
  field_simp

/-- **`tileslargemaxprop`** ([O+] L2521-L2525): there is `K`, depending
only on `N ≥ 2` (and not on `r`), such that for `2 ≤ r < ∞`, `λ > 0` and `S, I₀, F, f, ℓ` as above,
`(∑_{P ∈ S} |⟨f, φ_P⟩|^r)^{1/r} ≤ K (2^ℓ λ)^{1/r'} |I₀|^{1/2}` (`r' = r/(r-1)`). -/
theorem exists_rpow_sum_norm_coeff_le (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} (ch : ProfileChoice) (S : Finset (Multitile ρ)) {I₀ : Dyadic},
      (∀ P ∈ S, P.I = I₀) → ∀ {F : Set ℝ} {f : ℝ → ℂ}, MeasurableSet F →
      AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
      ∀ {lam : ℝ}, 0 < lam → ∀ {ℓ : ℕ}, ¬ I₀.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam →
      ∀ {r : ℝ}, 2 ≤ r →
        (∑ P ∈ S, ‖P.coeff ch f‖ ^ r) ^ (1 / r) ≤
          K * (2 ^ ℓ * lam) ^ (1 / Real.conjExponent r) * √I₀.length := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_coeff_le_sup
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_sqrt_sum_norm_sq_coeff_le N hN
  set K₀ : ℝ := max K₁ K₂ + 1 with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  refine ⟨K₀, hK₀pos.le, ?_⟩
  intro ρ ch S I₀ hS F f hF hfm hfF lam hlam ℓ h r hr
  have hr0 : 0 < r := by linarith
  have hL := I₀.length_pos
  set L := I₀.length with hLdef
  set u : ℝ := 2 ^ ℓ * lam with hu
  have hu0 : 0 < u := by positivity
  set X : ℝ := K₀ * u * √L with hX
  have hX0 : 0 < X := by positivity
  -- the sup bound
  have hsup : ∀ P ∈ S, ‖P.coeff ch f‖ ≤ X := by
    intro P hP
    have hPI := hS P hP
    have h' : ¬ P.I.dilate ((2 : ℝ) ^ (ℓ + 1)) ⊆ maxSuperlevel F lam := by rw [hPI]; exact h
    have := hK₁ ch P hF hfF hlam.le h'
    rw [hPI] at this
    refine this.trans ?_
    have h1 : K₁ ≤ K₀ := by rw [hK₀]; linarith [le_max_left K₁ K₂]
    rw [hX]
    gcongr
  -- the `ℓ²` bound
  have hsq : ∑ P ∈ S, ‖P.coeff ch f‖ ^ 2 ≤ X ^ 2 / u := by
    have h1 := hK₂ ch S hS hF hfm hfF hlam.le h
    have h2 : ∑ P ∈ S, ‖P.coeff ch f‖ ^ 2 ≤ (K₂ * √(u * L)) ^ 2 := by
      have h3 : 0 ≤ K₂ * √(u * L) := by positivity
      have := (Real.sqrt_le_left h3).1 h1
      exact this
    refine h2.trans ?_
    have h4 : K₂ ≤ K₀ := by rw [hK₀]; linarith [le_max_right K₁ K₂]
    have hs : √(u * L) ^ 2 = u * L := Real.sq_sqrt (by positivity)
    have hsL : √L ^ 2 = L := Real.sq_sqrt hL.le
    calc (K₂ * √(u * L)) ^ 2 = K₂ ^ 2 * (u * L) := by rw [mul_pow, hs]
      _ ≤ K₀ ^ 2 * (u * L) := by gcongr
      _ = X ^ 2 / u := by
          rw [hX, mul_pow, mul_pow, hsL]
          field_simp
  have hnn : ∀ P ∈ S, 0 ≤ ‖P.coeff ch f‖ := fun P _ => norm_nonneg _
  have hrpow := sum_rpow_le_of_sup_le_of_sum_sq_le S (fun P => ‖P.coeff ch f‖) hr hnn hX0.le hsup
    hsq
  -- `X^{r-2} X^2 / u = (X u^{-1/r})^r`
  set T : ℝ := X * u ^ (-(1 / r)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hTr : T ^ r = X ^ (r - 2) * (X ^ 2 / u) := by
    rw [hT, Real.mul_rpow hX0.le (by positivity), ← Real.rpow_mul hu0.le]
    have e1 : -(1 / r) * r = -1 := by field_simp
    rw [e1, Real.rpow_neg_one]
    have e2 : X ^ r = X ^ (r - 2) * X ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hX0]
      norm_num
    rw [e2]
    field_simp
  have hmain : (∑ P ∈ S, ‖P.coeff ch f‖ ^ r) ^ (1 / r) ≤ T := by
    have h1 : ∑ P ∈ S, ‖P.coeff ch f‖ ^ r ≤ T ^ r := by rw [hTr]; exact hrpow
    have h2 := Real.rpow_le_rpow (Finset.sum_nonneg fun P _ => by positivity) h1
      (by positivity : (0 : ℝ) ≤ 1 / r)
    rw [one_div, Real.rpow_rpow_inv hT0 hr0.ne'] at h2
    rw [one_div]
    exact h2
  refine hmain.trans (le_of_eq ?_)
  rw [one_div_conjExponent_eq (by linarith), hT, hX]
  have e3 : u ^ (1 - 1 / r) = u * u ^ (-(1 / r)) := by
    rw [sub_eq_add_neg, Real.rpow_add hu0, Real.rpow_one]
  rw [e3]
  ring

end PrimeCarleson.Proof.Oplus
