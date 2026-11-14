module

public import PrimeCarleson.Proof.Lepingle.Prob.DavisDecomposition
public import PrimeCarleson.Proof.Lepingle.Prob.Orthogonality
public import PrimeCarleson.Proof.Lepingle.Prob.LayerCake

/-!
# Davis' inequality: the bound `E Sf ≤ 27 E Mf`

Source: Zorin-Kranich's notes `thm:Davis-L1` (01-BDG.tex, L284–L291): Theorem 1.10 (L284-L371).
Only the half that is used downstream (`bdg_sqFn_le`) is proved: `E Sf ≲ E Mf` for a martingale
with `f_0 = 0`.
The converse half `E Mf ≲ E Sf` is *not* proved (it is unused, and the source only calls its proof
"similar", L363-L370).

The proof follows Zorin-Kranich's notes, L296-L361 with the constants `3 E Mf^pred + 4 E Mdf` etc.,
at a finite horizon `N` (so no "constant after `N`" reduction is needed):

* `sum_sq_le_sq_sum`, `sqUpTo_le_add`: `ℓ² ≤ ℓ¹` and Minkowski for the square function;
* `lintegral_Ioi_inv_sq_mul_le`: the calculus step `∫_0^∞ λ^{-2} ∫_{M ≤ λ} M² dλ ≤ E M`;
* `lintegral_sqUpTo_le_of_predictable_bound` (the core of L303-L343): for a martingale `P` with
  `P_0 = 0` and a predictable bound `‖P_{k+1}‖ ≤ ρ_k` (`ρ_k` is `ℱ k`-measurable),
  `E S P_N ≤ E M P_N + 2 E max_{k<N} ρ_k`.  The stopping time `τ = inf {n | ρ_n > λ}` is replaced
  by its predictable level sets `C_k = {ρ_j ≤ λ for j ≤ k}`, and the stopped martingale is the
  transform `∑_{k<n} 1_{C_k} dP_{k+1}` (`martingale_indicator_incr`);
* `lintegral_sqUpTo_le_davis`: `∫⁻ S f_N ≤ 3 ∫⁻ M f_N + 12 ∫⁻ Mdf_N ≤ 27 ∫⁻ M f_N`;
* `lintegral_sqFn_le_davis`: the same for `Sf = sup_N S f_N` and `Mf = sup_N M f_N`.

No integrability hypothesis is needed: all quantities take values in `ℝ≥0∞` and a martingale is
integrable at each time by definition.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

section Elementary

/-- `ℓ² ≤ ℓ¹` for finite sums in `ℝ≥0∞`: `∑ aᵢ² ≤ (∑ aᵢ)²`. -/
theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    ∑ i ∈ s, a i ^ 2 ≤ (∑ i ∈ s, a i) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => a i * a j) (fun _ _ => zero_le) hi

/-- `(∑ aᵢ²)^{1/2} ≤ ∑ aᵢ` in `ℝ≥0∞`. -/
theorem sqrt_sum_sq_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    (∑ i ∈ s, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ ∑ i ∈ s, a i := by
  have h := sum_sq_le_sq_sum s a
  simp_rw [← ENNReal.rpow_two] at h
  calc (∑ i ∈ s, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ((∑ i ∈ s, a i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = ∑ i ∈ s, a i := by
        rw [← ENNReal.rpow_mul]
        norm_num

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E]

/-- Minkowski for the square function: if `df = dg + dh` up to time `n`, then
`S f_n ≤ S g_n + S h_n`. -/
theorem sqUpTo_le_add {f g h : ℕ → Ω → E} {n : ℕ} {ω : Ω}
    (hfgh : ∀ k < n, incr f k ω = incr g k ω + incr h k ω) :
    sqUpTo f n ω ≤ sqUpTo g n ω + sqUpTo h n ω := by
  unfold sqUpTo
  calc (∑ k ∈ range n, ‖incr f k ω‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∑ k ∈ range n, (‖incr g k ω‖ₑ + ‖incr h k ω‖ₑ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun k hk => ?_) (by norm_num)
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [hfgh k (Finset.mem_range.1 hk)]
        exact enorm_add_le _ _
    _ ≤ _ := ENNReal.Lp_add_le (range n) (fun k => ‖incr g k ω‖ₑ) (fun k => ‖incr h k ω‖ₑ)
        (by norm_num)

/-- `S g_n ≤ ∑_{k<n} ‖dg_k‖`. -/
theorem sqUpTo_le_sum {g : ℕ → Ω → E} {n : ℕ} {ω : Ω} :
    sqUpTo g n ω ≤ ∑ k ∈ range n, ‖incr g k ω‖ₑ :=
  sqrt_sum_sq_le_sum (range n) fun k => ‖incr g k ω‖ₑ

theorem maxUpTo_lt_top' {g : ℕ → Ω → E} (n : ℕ) (ω : Ω) : maxUpTo g n ω < ∞ := by
  unfold maxUpTo
  rw [Finset.sup_lt_iff (by simp)]
  intro k _
  exact enorm_lt_top

end Elementary

section Calculus

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- For `a > 0`, `∫_{t > 0, t ≥ a} t^{-2} dt = 1/a` in `ℝ≥0∞`. -/
theorem lintegral_Ioi_indicator_inv_sq {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Set.Ioi (0 : ℝ), {t : ℝ | a ≤ t}.indicator
      (fun t => ENNReal.ofReal (t ^ (-2 : ℝ))) t = ENNReal.ofReal a⁻¹ := by
  have h1 : ∫⁻ t in Set.Ioi (0 : ℝ), {t : ℝ | a ≤ t}.indicator
      (fun t => ENNReal.ofReal (t ^ (-2 : ℝ))) t =
      ∫⁻ t in Set.Ici a, ENNReal.ofReal (t ^ (-2 : ℝ)) := by
    rw [← lintegral_indicator (measurableSet_Ici : MeasurableSet (Set.Ici a)),
      ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun t => ?_
    by_cases h : a ≤ t
    · have : 0 < t := ha.trans_le h
      simp [Set.indicator, h, this]
    · simp [Set.indicator, h]
  rw [h1, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  exact lintegral_Ioi_rpow_neg_two ha

/-- The calculus step of the Davis inequality (Zorin-Kranich's notes, L336-L342):
`∫_0^∞ λ^{-2} ∫_{M ≤ λ} M² dμ dλ ≤ ∫ M dμ` for a finite measurable `M ≥ 0`. -/
theorem lintegral_Ioi_inv_sq_mul_le [SFinite μ] {M : Ω → ℝ≥0∞} (hM : Measurable M)
    (hMfin : ∀ ω, M ω ≠ ∞) :
    ∫⁻ l in Set.Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-2 : ℝ)) *
      ∫⁻ ω, {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω ∂μ ≤
      ∫⁻ ω, M ω ∂μ := by
  have hmeas : Measurable (Function.uncurry fun (l : ℝ) (ω : Ω) =>
      {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => ENNReal.ofReal (l ^ (-2 : ℝ)) * M ω ^ 2)
        ω) := by
    have hs : MeasurableSet {q : ℝ × Ω | M q.2 ≤ ENNReal.ofReal q.1} :=
      measurableSet_le (hM.comp measurable_snd) (by fun_prop)
    have : Function.uncurry (fun (l : ℝ) (ω : Ω) =>
        {ω | M ω ≤ ENNReal.ofReal l}.indicator
          (fun ω => ENNReal.ofReal (l ^ (-2 : ℝ)) * M ω ^ 2) ω) =
        {q : ℝ × Ω | M q.2 ≤ ENNReal.ofReal q.1}.indicator
          (fun q => ENNReal.ofReal (q.1 ^ (-2 : ℝ)) * M q.2 ^ 2) := by
      funext q
      simp [Set.indicator, Function.uncurry]
    rw [this]
    refine Measurable.indicator ?_ hs
    exact (by fun_prop : Measurable fun q : ℝ × Ω => ENNReal.ofReal (q.1 ^ (-2 : ℝ))).mul
      ((hM.comp measurable_snd).pow_const _)
  have hin : ∀ l : ℝ, ENNReal.ofReal (l ^ (-2 : ℝ)) *
      ∫⁻ ω, {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω ∂μ =
      ∫⁻ ω, {ω | M ω ≤ ENNReal.ofReal l}.indicator
        (fun ω => ENNReal.ofReal (l ^ (-2 : ℝ)) * M ω ^ 2) ω ∂μ := by
    intro l
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    by_cases h : M ω ≤ ENNReal.ofReal l <;> simp [Set.indicator, h]
  simp_rw [hin]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_mono fun ω => ?_
  by_cases h0 : M ω = 0
  · simp [Set.indicator, h0]
  · set a : ℝ := (M ω).toReal with ha
    have hapos : 0 < a := ENNReal.toReal_pos h0 (hMfin ω)
    have hpt : ∀ l : ℝ, {ω' | M ω' ≤ ENNReal.ofReal l}.indicator
        (fun ω' => ENNReal.ofReal (l ^ (-2 : ℝ)) * M ω' ^ 2) ω =
        M ω ^ 2 * {l : ℝ | a ≤ l}.indicator (fun l => ENNReal.ofReal (l ^ (-2 : ℝ))) l := by
      intro l
      have hiff : M ω ≤ ENNReal.ofReal l ↔ a ≤ l := by
        by_cases hl : 0 ≤ l
        · exact ENNReal.le_ofReal_iff_toReal_le (hMfin ω) hl
        · have : ¬ M ω ≤ ENNReal.ofReal l := by
            rw [ENNReal.ofReal_of_nonpos (not_le.1 hl).le]
            simpa using h0
          simp only [this, false_iff, not_le]
          linarith
      by_cases hl : a ≤ l
      · simp [Set.indicator, hiff.2 hl, hl, mul_comm]
      · have : ¬ M ω ≤ ENNReal.ofReal l := fun h => hl (hiff.1 h)
        simp [Set.indicator, this, hl]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (hMfin ω)),
      lintegral_Ioi_indicator_inv_sq hapos, ENNReal.ofReal_inv_of_pos hapos,
      ha, ENNReal.ofReal_toReal (hMfin ω), sq, mul_assoc, ENNReal.mul_inv_cancel h0 (hMfin ω),
      mul_one]

end Calculus

section Core

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {𝕜 : Type*} [RCLike 𝕜]

/-- The running supremum `sup_{k<N} u_k` of a sequence of `ℝ≥0∞`-valued functions. -/
def supUpTo (u : ℕ → Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) : ℝ≥0∞ := (range N).sup fun k => u k ω

theorem supUpTo_zero (u : ℕ → Ω → ℝ≥0∞) (ω : Ω) : supUpTo u 0 ω = 0 := by
  simp [supUpTo]

theorem supUpTo_succ (u : ℕ → Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) :
    supUpTo u (N + 1) ω = max (supUpTo u N ω) (u N ω) := by
  simp only [supUpTo, Finset.range_add_one, Finset.sup_insert]
  rw [max_comm]

theorem measurable_supUpTo {u : ℕ → Ω → ℝ≥0∞} (hu : ∀ k, Measurable (u k)) (N : ℕ) :
    Measurable (supUpTo u N) := by
  induction N with
  | zero =>
    have : supUpTo u 0 = fun _ => 0 := funext (supUpTo_zero u)
    rw [this]
    exact measurable_const
  | succ N ih =>
    have : supUpTo u (N + 1) = fun ω => max (supUpTo u N ω) (u N ω) :=
      funext (supUpTo_succ u N)
    rw [this]
    exact ih.max (hu N)

theorem lt_supUpTo_iff {u : ℕ → Ω → ℝ≥0∞} {N : ℕ} {c : ℝ≥0∞} {ω : Ω} :
    c < supUpTo u N ω ↔ ∃ k < N, c < u k ω := by
  simp [supUpTo, Finset.lt_sup_iff]

theorem supUpTo_le_iff {u : ℕ → Ω → ℝ≥0∞} {N : ℕ} {c : ℝ≥0∞} {ω : Ω} :
    supUpTo u N ω ≤ c ↔ ∀ k < N, u k ω ≤ c := by
  simp [supUpTo, Finset.sup_le_iff]

/-- **The core of Davis' inequality** (Zorin-Kranich's notes, L303-L343, with the stopping time
`τ = inf {n | ρ_n > λ}` replaced by its predictable level sets).  Let `P` be a martingale with
`P_0 = 0` and a predictable bound `‖P_{k+1}‖ ≤ ρ_k` with `ρ_k` `ℱ k`-measurable.  Then
`E S P_N ≤ E M P_N + 2 E max_{k<N} ρ_k`. -/
theorem lintegral_sqUpTo_le_of_predictable_bound [IsFiniteMeasure μ]
    {P : ℕ → Ω → 𝕜} (hP : Martingale P ℱ μ) (hP0 : P 0 = 0)
    {ρ : ℕ → Ω → ℝ} (hρ : ∀ k, Measurable[ℱ k] (ρ k))
    (hbd : ∀ᵐ ω ∂μ, ∀ k, ‖P (k + 1) ω‖ ≤ ρ k ω) (N : ℕ) :
    ∫⁻ ω, sqUpTo P N ω ∂μ ≤ ∫⁻ ω, maxUpTo P N ω ∂μ +
      2 * ∫⁻ ω, supUpTo (fun k ω => ENNReal.ofReal (ρ k ω)) N ω ∂μ := by
  have hPm : ∀ k, Measurable (P k) := fun k =>
    (hP.stronglyMeasurable k).measurable.mono (ℱ.le k) le_rfl
  have hρm : ∀ k, Measurable (ρ k) := fun k => (hρ k).mono (ℱ.le k) le_rfl
  set S := sqUpTo P N with hS
  set M := maxUpTo P N with hM
  set R := supUpTo (fun k ω => ENNReal.ofReal (ρ k ω)) N with hR
  have hSm : Measurable S := measurable_sqUpTo fun k _ => hPm k
  have hMm : Measurable M := measurable_maxUpTo fun k _ => hPm k
  have hRm : Measurable R := measurable_supUpTo (fun k => (hρm k).ennreal_ofReal) N
  have hMfin : ∀ ω, M ω ≠ ∞ := fun ω => (maxUpTo_lt_top' N ω).ne
  -- the bound for each level `l > 0`
  have key : ∀ l : ℝ, 0 < l → μ {ω | ENNReal.ofReal l < S ω} ≤
      ENNReal.ofReal (l ^ (-2 : ℝ)) *
        ∫⁻ ω, {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω ∂μ +
      2 * μ {ω | ENNReal.ofReal l < R ω} := by
    intro l hl
    set D : Set Ω := {ω | ∀ j < N, ρ j ω ≤ l} with hD
    have hDm : MeasurableSet D := by
      have : D = ⋂ j ∈ Finset.range N, {ω | ρ j ω ≤ l} := by
        ext ω
        simp [hD]
      rw [this]
      exact Finset.measurableSet_biInter _ fun j _ => measurableSet_le (hρm j) measurable_const
    have hDcompl : Dᶜ = {ω | ENNReal.ofReal l < R ω} := by
      ext ω
      simp only [hD, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le, hR, lt_supUpTo_iff]
      constructor
      · rintro ⟨j, hj, h⟩
        exact ⟨j, hj, (ENNReal.ofReal_lt_ofReal_iff (hl.trans h)).2 h⟩
      · rintro ⟨j, hj, h⟩
        exact ⟨j, hj, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hl.le).1 h⟩
    -- the predictable level sets and the transform `G = P^{(τ)}`
    set C : ℕ → Set Ω := fun k => {ω | ∀ j < k + 1, ρ j ω ≤ l} with hC
    have hCm : ∀ k, MeasurableSet[ℱ k] (C k) := by
      intro k
      have : C k = ⋂ j ∈ Finset.range (k + 1), {ω | ρ j ω ≤ l} := by
        ext ω
        simp [hC]
      rw [this]
      refine Finset.measurableSet_biInter _ fun j hj => ?_
      exact measurableSet_le ((hρ j).mono (ℱ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
        le_rfl) measurable_const
    set G : ℕ → Ω → 𝕜 := fun n ω => ∑ k ∈ Finset.range n, (C k).indicator (incr P k) ω with hGdef
    have hG : Martingale G ℱ μ := martingale_indicator_incr hP hCm
    have hGm : ∀ k, Measurable (G k) := fun k =>
      (hG.stronglyMeasurable k).measurable.mono (ℱ.le k) le_rfl
    have hG0 : G 0 = 0 := by
      funext ω
      simp [hGdef]
    have hGincr : ∀ k ω, incr G k ω = (C k).indicator (incr P k) ω := by
      intro k ω
      simp [incr_apply, hGdef, Finset.sum_range_succ]
    have hGclaim : ∀ ω, (∀ k, ‖P (k + 1) ω‖ ≤ ρ k ω) → ∀ n,
        (ω ∈ {ω | ∀ j < n, ρ j ω ≤ l} → G n ω = P n ω) ∧ ‖G n ω‖ ≤ l := by
      intro ω hω n
      induction n with
      | zero =>
        refine ⟨fun _ => ?_, ?_⟩
        · simp [hGdef, hP0]
        · simpa [hGdef] using hl.le
      | succ n ih =>
        by_cases hmem : ω ∈ C n
        · have hmem' : ω ∈ {ω | ∀ j < n, ρ j ω ≤ l} := fun j hj => hmem j (by omega)
          have h1 : G n ω = P n ω := ih.1 hmem'
          have h2 : G (n + 1) ω = P (n + 1) ω := by
            have : G (n + 1) ω = G n ω + incr P n ω := by
              simp [hGdef, Finset.sum_range_succ, Set.indicator_of_mem hmem]
            rw [this, h1, incr_apply]
            ring
          refine ⟨fun _ => h2, ?_⟩
          rw [h2]
          exact (hω n).trans (hmem n (by omega))
        · have h2 : G (n + 1) ω = G n ω := by
            simp [hGdef, Finset.sum_range_succ, Set.indicator_of_notMem hmem]
          exact ⟨fun h => absurd h hmem, by rw [h2]; exact ih.2⟩
    have hGbd : ∀ᵐ ω ∂μ, ∀ n, ‖G n ω‖ ≤ l := by
      filter_upwards [hbd] with ω hω n using (hGclaim ω hω n).2
    have hGL2 : MemLp (G N) 2 μ :=
      MemLp.of_bound (hGm N).aestronglyMeasurable l (by filter_upwards [hGbd] with ω hω using hω N)
    -- orthogonality and Chebyshev for `G`
    set SG := sqUpTo G N with hSG
    have hSGm : Measurable SG := measurable_sqUpTo fun k _ => hGm k
    have horth : ∫⁻ ω, SG ω ^ 2 ∂μ = ∫⁻ ω, ‖G N ω‖ₑ ^ 2 ∂μ := by
      have := lintegral_sqUpTo_sq_eq hG hGL2
      simpa only [hG0, Pi.zero_apply, sub_zero, ENNReal.rpow_two] using this
    have hcheb : ENNReal.ofReal l ^ 2 * μ {ω | ENNReal.ofReal l < SG ω} ≤
        ∫⁻ ω, ‖G N ω‖ₑ ^ 2 ∂μ := by
      rw [← horth]
      calc ENNReal.ofReal l ^ 2 * μ {ω | ENNReal.ofReal l < SG ω}
          = ∫⁻ ω in {ω | ENNReal.ofReal l < SG ω}, ENNReal.ofReal l ^ 2 ∂μ :=
            (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ ω in {ω | ENNReal.ofReal l < SG ω}, SG ω ^ 2 ∂μ :=
            setLIntegral_mono' (measurableSet_lt measurable_const hSGm) fun ω hω =>
              pow_le_pow_left' hω.le 2
        _ ≤ ∫⁻ ω, SG ω ^ 2 ∂μ := setLIntegral_le_lintegral _ _
    -- bound `‖G_N‖²` by the two pieces
    have hGN : ∫⁻ ω, ‖G N ω‖ₑ ^ 2 ∂μ ≤
        ∫⁻ ω, {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω ∂μ +
          ENNReal.ofReal l ^ 2 * μ Dᶜ := by
      have hae : ∀ᵐ ω ∂μ, ‖G N ω‖ₑ ^ 2 ≤
          {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω +
            Dᶜ.indicator (fun _ => ENNReal.ofReal l ^ 2) ω := by
        filter_upwards [hbd] with ω hω
        by_cases hωD : ω ∈ D
        · have h1 : G N ω = P N ω := (hGclaim ω hω N).1 hωD
          have hMle : M ω ≤ ENNReal.ofReal l := by
            refine maxUpTo_le_iff.2 fun k hk => ?_
            rcases k with _ | j
            · simp [hP0]
            · rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal ((hω j).trans (hωD j (by omega)))
          have hPN : ‖P N ω‖ₑ ≤ M ω := le_maxUpTo le_rfl
          rw [Set.indicator_of_mem (show ω ∈ {ω | M ω ≤ ENNReal.ofReal l} from hMle), h1]
          exact le_add_right (pow_le_pow_left' hPN 2)
        · have hωDc : ω ∈ Dᶜ := hωD
          rw [Set.indicator_of_mem hωDc]
          refine le_add_left (pow_le_pow_left' ?_ 2)
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal ((hGclaim ω hω N).2)
      calc ∫⁻ ω, ‖G N ω‖ₑ ^ 2 ∂μ
          ≤ ∫⁻ ω, ({ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω +
              Dᶜ.indicator (fun _ => ENNReal.ofReal l ^ 2) ω) ∂μ := lintegral_mono_ae hae
        _ = _ := by
            rw [lintegral_add_left ((hMm.pow_const 2).indicator
              (measurableSet_le hMm measurable_const)), lintegral_indicator_const hDm.compl]
    -- `{l < S} ⊆ {l < SG} ∪ Dᶜ`
    have hsub : {ω | ENNReal.ofReal l < S ω} ⊆ {ω | ENNReal.ofReal l < SG ω} ∪ Dᶜ := by
      intro ω hω
      by_cases hωD : ω ∈ D
      · left
        have : SG ω = S ω := by
          simp only [hSG, hS, sqUpTo]
          refine congrArg (· ^ (1 / 2 : ℝ)) (Finset.sum_congr rfl fun k hk => ?_)
          have hkN : k < N := Finset.mem_range.1 hk
          have hmem : ω ∈ C k := fun j hj => hωD j (by omega)
          rw [hGincr, Set.indicator_of_mem hmem]
        rw [Set.mem_ofPred_eq, this]
        exact hω
      · right
        exact hωD
    have hinv : ENNReal.ofReal (l ^ (-2 : ℝ)) * ENNReal.ofReal l ^ 2 = 1 := by
      rw [← ENNReal.ofReal_pow hl.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hl.le _)]
      have : l ^ (-2 : ℝ) * l ^ 2 = 1 := by
        rw [Real.rpow_neg hl.le, Real.rpow_two]
        exact inv_mul_cancel₀ (by positivity)
      rw [this]
      simp
    set B := ∫⁻ ω, {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω ∂μ with hB
    have hSGle : μ {ω | ENNReal.ofReal l < SG ω} ≤
        ENNReal.ofReal (l ^ (-2 : ℝ)) * B + μ Dᶜ := by
      calc μ {ω | ENNReal.ofReal l < SG ω}
          = ENNReal.ofReal (l ^ (-2 : ℝ)) *
            (ENNReal.ofReal l ^ 2 * μ {ω | ENNReal.ofReal l < SG ω}) := by
            rw [← mul_assoc, hinv, one_mul]
        _ ≤ ENNReal.ofReal (l ^ (-2 : ℝ)) * (B + ENNReal.ofReal l ^ 2 * μ Dᶜ) :=
            mul_le_mul_right (hcheb.trans hGN) _
        _ = ENNReal.ofReal (l ^ (-2 : ℝ)) * B + μ Dᶜ := by
            rw [mul_add, ← mul_assoc, hinv, one_mul]
    calc μ {ω | ENNReal.ofReal l < S ω}
        ≤ μ ({ω | ENNReal.ofReal l < SG ω} ∪ Dᶜ) := measure_mono hsub
      _ ≤ μ {ω | ENNReal.ofReal l < SG ω} + μ Dᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (l ^ (-2 : ℝ)) * B + μ Dᶜ + μ Dᶜ := by gcongr
      _ = ENNReal.ofReal (l ^ (-2 : ℝ)) * B + 2 * μ Dᶜ := by
          rw [add_assoc, ← two_mul]
      _ = _ := by rw [hDcompl]
  -- integrate over `l`
  have hanti : Antitone fun l : ℝ => μ {ω | ENNReal.ofReal l < R ω} := fun l l' hll' =>
    measure_mono fun ω hω => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hll') hω
  calc ∫⁻ ω, S ω ∂μ
      = ∫⁻ l in Set.Ioi (0 : ℝ), μ {ω | ENNReal.ofReal l < S ω} :=
        lintegral_eq_lintegral_meas_lt_ennreal hSm
    _ ≤ ∫⁻ l in Set.Ioi (0 : ℝ), (ENNReal.ofReal (l ^ (-2 : ℝ)) *
          ∫⁻ ω, {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω ∂μ +
          2 * μ {ω | ENNReal.ofReal l < R ω}) :=
        setLIntegral_mono' measurableSet_Ioi fun l hl => key l hl
    _ = (∫⁻ l in Set.Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-2 : ℝ)) *
          ∫⁻ ω, {ω | M ω ≤ ENNReal.ofReal l}.indicator (fun ω => M ω ^ 2) ω ∂μ) +
        2 * ∫⁻ l in Set.Ioi (0 : ℝ), μ {ω | ENNReal.ofReal l < R ω} := by
        rw [lintegral_add_right _ (hanti.measurable.const_mul 2),
          lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ ∫⁻ ω, M ω ∂μ + 2 * ∫⁻ ω, R ω ∂μ := by
        rw [lintegral_eq_lintegral_meas_lt_ennreal hRm]
        gcongr
        exact lintegral_Ioi_inv_sq_mul_le hMm hMfin

end Core

section Davis

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

/-- `Mdf_N ≤ 2 Mf_N` (the increments are differences of two values of `f`). -/
theorem ofReal_incrMax_le_two_mul_maxUpTo (f : ℕ → Ω → 𝕜) (N : ℕ) (ω : Ω) :
    ENNReal.ofReal (incrMax f N ω) ≤ 2 * maxUpTo f N ω := by
  refine ofReal_incrMax_le fun j hj => ?_
  calc ‖incr f j ω‖ₑ ≤ ‖f (j + 1) ω‖ₑ + ‖f j ω‖ₑ := enorm_sub_le
    _ ≤ maxUpTo f N ω + maxUpTo f N ω :=
        add_le_add (le_maxUpTo (Nat.succ_le_of_lt hj)) (le_maxUpTo hj.le)
    _ = 2 * maxUpTo f N ω := (two_mul _).symm

/-- `‖Q_n - Q_0‖ ≤ ∑_{k<n} ‖Q_{k+1} - Q_k‖`. -/
theorem enorm_sub_zero_le_sum_enorm_incr (Q : ℕ → Ω → 𝕜) (n : ℕ) (ω : Ω) :
    ‖Q n ω - Q 0 ω‖ₑ ≤ ∑ k ∈ range n, ‖incr Q k ω‖ₑ := by
  have : Q n ω - Q 0 ω = ∑ k ∈ range n, incr Q k ω :=
    (Finset.sum_range_sub (fun k => Q k ω) n).symm
  rw [this]
  exact enorm_sum_le _ _

/-- **Davis' inequality, finite horizon** (Zorin-Kranich's notes, Theorem 1.10, the written half
`E Sf ≲ E Mf`): for a martingale with `f_0 = 0`,
`E S f_N ≤ 3 E M f_N + 12 E Mdf_N`. -/
theorem lintegral_sqUpTo_le_davis_aux [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) (hf0 : f 0 = 0)
    (N : ℕ) :
    ∫⁻ ω, sqUpTo f N ω ∂μ ≤
      3 * ∫⁻ ω, maxUpTo f N ω ∂μ + 12 * ∫⁻ ω, ENNReal.ofReal (incrMax f N ω) ∂μ := by
  obtain ⟨P, Q, hP, hQ, hP0, hQ0, hfPQ, hjump, hvar⟩ := davis_decomposition hf
  have hm : ∀ j, Measurable (f j) := fun j =>
    (hf.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl
  have hmℱ : ∀ k, ∀ j ≤ k, Measurable[ℱ k] (f j) := fun k j hj =>
    ((hf.stronglyMeasurable j).mono (ℱ.mono hj)).measurable
  have hPm : ∀ k, Measurable (P k) := fun k =>
    (hP.stronglyMeasurable k).measurable.mono (ℱ.le k) le_rfl
  have hQm : ∀ k, Measurable (Q k) := fun k =>
    (hQ.stronglyMeasurable k).measurable.mono (ℱ.le k) le_rfl
  have hDm : Measurable fun ω => ENNReal.ofReal (incrMax f N ω) :=
    (measurable_incrMax fun j _ => hm j).ennreal_ofReal
  set d := ∫⁻ ω, ENNReal.ofReal (incrMax f N ω) ∂μ with hd
  set mf := ∫⁻ ω, maxUpTo f N ω ∂μ with hmf
  set a := ∫⁻ ω, maxUpTo P N ω ∂μ with ha
  set q := ∫⁻ ω, ∑ k ∈ range N, ‖incr Q k ω‖ₑ ∂μ with hq
  -- the predictable bound `ρ_k = ‖P_k‖ + 2 Mdf_k`
  let ρ : ℕ → Ω → ℝ := fun k ω => ‖P k ω‖ + 2 * incrMax f k ω
  have hρ : ∀ k, Measurable[ℱ k] (ρ k) := by
    intro k
    have h2 : Measurable[ℱ k] (incrMax f k) :=
      measurable_incrMax (m := ℱ k) fun j hj => hmℱ k j hj
    exact ((hP.stronglyMeasurable k).norm.add (h2.stronglyMeasurable.const_mul 2)).measurable
  have hbd : ∀ᵐ ω ∂μ, ∀ k, ‖P (k + 1) ω‖ ≤ ρ k ω := by
    filter_upwards [hjump] with ω hω k
    have : P (k + 1) ω = P k ω + incr P k ω := by simp [incr_apply]
    calc ‖P (k + 1) ω‖ = ‖P k ω + incr P k ω‖ := by rw [this]
      _ ≤ ‖P k ω‖ + ‖incr P k ω‖ := norm_add_le _ _
      _ ≤ ρ k ω := add_le_add le_rfl (hω k)
  have hA := lintegral_sqUpTo_le_of_predictable_bound hP hP0 hρ hbd N
  have hMPm : Measurable (maxUpTo P N) := measurable_maxUpTo fun k _ => hPm k
  have hRle : ∀ ω, supUpTo (fun k ω => ENNReal.ofReal (ρ k ω)) N ω ≤
      maxUpTo P N ω + 2 * ENNReal.ofReal (incrMax f N ω) := by
    intro ω
    refine supUpTo_le_iff.2 fun k hk => ?_
    simp only [ρ]
    rw [ENNReal.ofReal_add (norm_nonneg _) (by have := incrMax_nonneg (f := f) k ω; positivity),
      ENNReal.ofReal_mul (by norm_num), ofReal_norm]
    gcongr
    · exact le_maxUpTo hk.le
    · simp only [ENNReal.ofReal_ofNat]
      exact le_rfl
    · exact incrMax_mono ω hk.le
  have hR : ∫⁻ ω, supUpTo (fun k ω => ENNReal.ofReal (ρ k ω)) N ω ∂μ ≤ a + 2 * d := by
    calc _ ≤ ∫⁻ ω, (maxUpTo P N ω + 2 * ENNReal.ofReal (incrMax f N ω)) ∂μ := lintegral_mono hRle
      _ = a + 2 * d := by
        rw [lintegral_add_left hMPm, lintegral_const_mul _ hDm]
  have hSP : ∫⁻ ω, sqUpTo P N ω ∂μ ≤ a + 2 * (a + 2 * d) :=
    hA.trans (add_le_add le_rfl (mul_le_mul_right hR 2))
  -- `M P_N ≤ M f_N + ∑ ‖dQ‖`
  have hMP : a ≤ mf + q := by
    have hae : ∀ᵐ ω ∂μ, maxUpTo P N ω ≤ maxUpTo f N ω + ∑ k ∈ range N, ‖incr Q k ω‖ₑ := by
      filter_upwards [hfPQ] with ω hω
      refine maxUpTo_le_iff.2 fun n hn => ?_
      have h1 : P n ω = f n ω - Q n ω := by
        have := hω n
        simp only [hf0, Pi.zero_apply, zero_add] at this
        rw [this]
        ring
      calc ‖P n ω‖ₑ = ‖f n ω - Q n ω‖ₑ := by rw [h1]
        _ ≤ ‖f n ω‖ₑ + ‖Q n ω‖ₑ := enorm_sub_le
        _ ≤ maxUpTo f N ω + ∑ k ∈ range N, ‖incr Q k ω‖ₑ := by
          refine add_le_add (le_maxUpTo hn) ?_
          have h0 : Q 0 = 0 := hQ0
          have := enorm_sub_zero_le_sum_enorm_incr Q n ω
          simp only [h0, Pi.zero_apply, sub_zero] at this
          exact this.trans (Finset.sum_le_sum_of_subset (Finset.range_mono hn))
    calc a ≤ ∫⁻ ω, (maxUpTo f N ω + ∑ k ∈ range N, ‖incr Q k ω‖ₑ) ∂μ := lintegral_mono_ae hae
      _ = mf + q := lintegral_add_left (measurable_maxUpTo fun k _ => hm k) _
  have hqle : q ≤ 2 * d := hvar N
  -- `S f ≤ S P + S Q`
  have hSf : ∫⁻ ω, sqUpTo f N ω ∂μ ≤ ∫⁻ ω, sqUpTo P N ω ∂μ + q := by
    have hae : ∀ᵐ ω ∂μ, sqUpTo f N ω ≤ sqUpTo P N ω + ∑ k ∈ range N, ‖incr Q k ω‖ₑ := by
      filter_upwards [hfPQ] with ω hω
      refine (sqUpTo_le_add (g := P) (h := Q) fun k _ => ?_).trans
        (add_le_add le_rfl sqUpTo_le_sum)
      simp only [incr_apply, hω k, hω (k + 1), hf0, Pi.zero_apply]
      ring
    calc ∫⁻ ω, sqUpTo f N ω ∂μ ≤ ∫⁻ ω, (sqUpTo P N ω + ∑ k ∈ range N, ‖incr Q k ω‖ₑ) ∂μ :=
          lintegral_mono_ae hae
      _ = _ := lintegral_add_left (measurable_sqUpTo fun k _ => hPm k) _
  calc ∫⁻ ω, sqUpTo f N ω ∂μ ≤ a + 2 * (a + 2 * d) + q := hSf.trans (add_le_add hSP le_rfl)
    _ = 3 * a + 4 * d + q := by ring
    _ ≤ 3 * (mf + q) + 4 * d + q := by gcongr
    _ = 3 * mf + 4 * q + 4 * d := by ring
    _ ≤ 3 * mf + 4 * (2 * d) + 4 * d := by gcongr
    _ = 3 * mf + 12 * d := by ring

/-- **Davis' inequality, finite horizon** (Zorin-Kranich's notes, Theorem 1.10, the written
half): for a martingale with `f_0 = 0`, `E S f_N ≤ 27 E M f_N`. -/
theorem lintegral_sqUpTo_le_davis [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) (hf0 : f 0 = 0)
    (N : ℕ) : ∫⁻ ω, sqUpTo f N ω ∂μ ≤ 27 * ∫⁻ ω, maxUpTo f N ω ∂μ := by
  refine (lintegral_sqUpTo_le_davis_aux hf hf0 N).trans ?_
  have h : ∫⁻ ω, ENNReal.ofReal (incrMax f N ω) ∂μ ≤ 2 * ∫⁻ ω, maxUpTo f N ω ∂μ := by
    calc _ ≤ ∫⁻ ω, 2 * maxUpTo f N ω ∂μ :=
          lintegral_mono fun ω => ofReal_incrMax_le_two_mul_maxUpTo f N ω
      _ = 2 * ∫⁻ ω, maxUpTo f N ω ∂μ :=
          lintegral_const_mul _ (measurable_maxUpTo fun k _ =>
            (hf.stronglyMeasurable k).measurable.mono (ℱ.le k) le_rfl)
  calc 3 * ∫⁻ ω, maxUpTo f N ω ∂μ + 12 * ∫⁻ ω, ENNReal.ofReal (incrMax f N ω) ∂μ
      ≤ 3 * ∫⁻ ω, maxUpTo f N ω ∂μ + 12 * (2 * ∫⁻ ω, maxUpTo f N ω ∂μ) := by gcongr
    _ = 27 * ∫⁻ ω, maxUpTo f N ω ∂μ := by ring

/-- **Davis' inequality** (Zorin-Kranich's notes, Theorem 1.10, the written half
`E Sf ≲ E Mf`): for a martingale with `f_0 = 0`, `E Sf ≤ 27 E Mf`, where
`Sf = (∑_k ‖df_k‖²)^{1/2}` and `Mf = sup_n ‖f_n‖`, in `ℝ≥0∞`. -/
theorem lintegral_sqFn_le_davis [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) (hf0 : f 0 = 0) :
    ∫⁻ ω, sqFn f ω ∂μ ≤ 27 * ∫⁻ ω, maxFn f ω ∂μ := by
  have hm : ∀ j, Measurable (f j) := fun j =>
    (hf.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl
  have : ∫⁻ ω, sqFn f ω ∂μ = ⨆ N, ∫⁻ ω, sqUpTo f N ω ∂μ := by
    unfold sqFn
    exact lintegral_iSup (fun N => measurable_sqUpTo fun k _ => hm k)
      fun N N' hNN' ω => sqUpTo_mono hNN'
  rw [this]
  exact iSup_le fun N => (lintegral_sqUpTo_le_davis hf hf0 N).trans
    (mul_le_mul_right (lintegral_mono fun ω => maxUpTo_le_maxFn N) 27)

end Davis

end PrimeCarleson.Proof.Lepingle
