module

public import PrimeCarleson.Proof.Lepingle.Prob.Martingale

/-!
# The Davis decomposition

Source: Zorin-Kranich's notes `lem:Davis-decomposition` (01-BDG.tex, L228–L240): Lemma 1.9
(L228-L282): every martingale `f` is a sum
`f = f^pred + f^bv` of two martingales with `|df^pred_n| ≤ 2 Mdf_{n-1}` and
`E ∑_n |df^bv_n| ≤ 2 E Mdf`.

Notation (increments `d_k = f_{k+1} - f_k = df_{k+1}`):
* `incrMax f k = max_{j<k} ‖d_j‖ = max_{1≤i≤k} ‖df_i‖` (`Mdf_k` of Zorin-Kranich's notes for
  `f_0 = 0`; the predictable bound for the increment `d_k = df_{k+1}`; `incrMax f 0 = 0`),
  `ℱ k`-measurable;
* the clipped increments `dg_k = min(1, Mdf_{k-1}/|df_k|) df_k` (`clipInc`) and
  `dh_k = df_k - dg_k`, with `‖dg_k‖ ≤ incrMax f k` and `‖dh_k‖ = incrMax f (k+1) - incrMax f k`
  (telescoping bound `|dh_n| = Mdf_n - Mdf_{n-1}`, Zorin-Kranich's notes, L273-L276);
* `df^pred_{k+1} = dg_k - E_k dg_k`, `df^bv_{k+1} = dh_k - E_k dh_k`.

The statement `davis_decomposition` is for an arbitrary martingale (no `f 0 = 0`): it gives
martingales `P, Q` with `P 0 = Q 0 = 0` and `f n = f 0 + P n + Q n` a.e.; for `f 0 = 0` this is
the notes' `f = f^pred + f^bv`.  The bounds are stated at finite horizon `N`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

section IncrMax

variable {E : Type*} [NormedAddCommGroup E] {f : ℕ → Ω → E}

/-- Running maximum of the increments: `incrMax f k ω = max_{j<k} ‖f_{j+1}(ω) - f_j(ω)‖` (`Mdf_k` of
Zorin-Kranich's notes for `f_0 = 0`, where `Mdf_n = max_{j≤n} ‖df_j‖`; it bounds the next increment
`d_k = df_{k+1}`, so it is the `Mdf_{(k+1)-1}` of the Davis decomposition), `incrMax f 0 = 0`. -/
def incrMax (f : ℕ → Ω → E) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω => max (incrMax f k ω) ‖incr f k ω‖

theorem incrMax_zero (f : ℕ → Ω → E) (ω : Ω) : incrMax f 0 ω = 0 := rfl

theorem incrMax_succ (f : ℕ → Ω → E) (k : ℕ) (ω : Ω) :
    incrMax f (k + 1) ω = max (incrMax f k ω) ‖incr f k ω‖ := rfl

theorem incrMax_nonneg (k : ℕ) (ω : Ω) : 0 ≤ incrMax f k ω := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (le_max_left _ _)

theorem incrMax_mono (ω : Ω) : Monotone fun k => incrMax f k ω :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

theorem incrMax_le_sum (k : ℕ) (ω : Ω) : incrMax f k ω ≤ ∑ j ∈ range k, ‖incr f j ω‖ := by
  induction k with
  | zero => simp [incrMax_zero]
  | succ k ih =>
    rw [incrMax_succ, Finset.sum_range_succ]
    refine max_le (ih.trans ?_) ?_
    · linarith [norm_nonneg (incr f k ω)]
    · linarith [Finset.sum_nonneg (fun j (_ : j ∈ range k) => norm_nonneg (incr f j ω))]

theorem ofReal_incrMax_le {k : ℕ} {ω : Ω} {c : ℝ≥0∞} (h : ∀ j < k, ‖incr f j ω‖ₑ ≤ c) :
    ENNReal.ofReal (incrMax f k ω) ≤ c := by
  induction k with
  | zero => simp [incrMax_zero]
  | succ k ih =>
    rw [incrMax_succ, ENNReal.ofReal_max]
    exact max_le (ih fun j hj => h j (hj.trans k.lt_succ_self))
      (by rw [ofReal_norm]; exact h k k.lt_succ_self)

end IncrMax

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

theorem measurable_incrMax {m : MeasurableSpace Ω} {k : ℕ} (hf : ∀ j ≤ k, Measurable (f j)) :
    Measurable (incrMax f k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have : incrMax f (k + 1) = fun ω => max (incrMax f k ω) ‖incr f k ω‖ := rfl
    rw [this]
    exact (ih fun j hj => hf j (hj.trans k.le_succ)).max
      ((((hf (k + 1) le_rfl)).sub (hf k k.le_succ))).norm

theorem integrable_incrMax [IsFiniteMeasure μ] (hm : ∀ j, Measurable (f j))
    (hi : ∀ j, Integrable (f j) μ) (k : ℕ) : Integrable (incrMax f k) μ := by
  refine Integrable.mono' (g := fun ω => ∑ j ∈ range k, ‖incr f j ω‖)
    (integrable_finsetSum _ fun j _ => ((hi (j + 1)).sub (hi j)).norm)
    (measurable_incrMax fun j _ => hm j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (incrMax_nonneg k ω)]
  exact incrMax_le_sum k ω

/-- The clipping factor `min(1, Mdf_{k-1}/|df_k|)` of the Davis decomposition (`∈ [0,1]`). -/
def clipFactor (f : ℕ → Ω → 𝕜) (k : ℕ) (ω : Ω) : ℝ :=
  min 1 (incrMax f k ω / ‖incr f k ω‖)

/-- The clipped increments `dg_k = min(1, Mdf_{k-1}/|df_k|) df_k`. -/
def clipInc (f : ℕ → Ω → 𝕜) (k : ℕ) (ω : Ω) : 𝕜 := clipFactor f k ω • incr f k ω

theorem clipFactor_nonneg (k : ℕ) (ω : Ω) : 0 ≤ clipFactor f k ω :=
  le_min zero_le_one (div_nonneg (incrMax_nonneg k ω) (norm_nonneg _))

theorem clipFactor_le_one (k : ℕ) (ω : Ω) : clipFactor f k ω ≤ 1 := min_le_left _ _

theorem norm_clipInc (k : ℕ) (ω : Ω) : ‖clipInc f k ω‖ = clipFactor f k ω * ‖incr f k ω‖ := by
  rw [clipInc, norm_smul, Real.norm_of_nonneg (clipFactor_nonneg k ω)]

/-- `‖dg_k‖ ≤ Mdf_{k-1}`. -/
theorem norm_clipInc_le (k : ℕ) (ω : Ω) : ‖clipInc f k ω‖ ≤ incrMax f k ω := by
  rw [norm_clipInc]
  rcases (norm_nonneg (incr f k ω)).eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact incrMax_nonneg k ω
  · calc clipFactor f k ω * ‖incr f k ω‖ ≤ incrMax f k ω / ‖incr f k ω‖ * ‖incr f k ω‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) h.le
      _ = incrMax f k ω := div_mul_cancel₀ _ h.ne'

/-- The telescoping bound `‖dh_k‖ = Mdf_k - Mdf_{k-1}` for `dh_k = df_k - dg_k`. -/
theorem norm_incr_sub_clipInc (k : ℕ) (ω : Ω) :
    ‖incr f k ω - clipInc f k ω‖ = incrMax f (k + 1) ω - incrMax f k ω := by
  have h1 : incr f k ω - clipInc f k ω = (1 - clipFactor f k ω) • incr f k ω := by
    simp [clipInc, sub_smul]
  rw [h1, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 (clipFactor_le_one k ω)), incrMax_succ]
  set a := ‖incr f k ω‖ with ha
  set D := incrMax f k ω with hD
  have hD0 : 0 ≤ D := incrMax_nonneg k ω
  rcases (norm_nonneg (incr f k ω)).eq_or_lt with h | h
  · rw [← ha] at h
    rw [← h]
    simp [hD0]
  · rw [← ha] at h
    rcases le_or_gt a D with hle | hlt
    · have : clipFactor f k ω = 1 := by
        refine le_antisymm (clipFactor_le_one k ω) (le_min le_rfl ?_)
        rw [le_div_iff₀ h]
        linarith
      rw [this, max_eq_left hle]
      simp
    · have : clipFactor f k ω = D / a := by
        refine min_eq_right ?_
        rw [div_le_one h]
        exact hlt.le
      rw [this, max_eq_right hlt.le]
      field_simp

theorem measurable_clipInc {m : MeasurableSpace Ω} {k : ℕ} (hf : ∀ j ≤ k + 1, Measurable (f j)) :
    Measurable (clipInc f k) := by
  have hi : Measurable (incr f k) := (hf (k + 1) le_rfl).sub (hf k k.le_succ)
  have hD : Measurable (incrMax f k) := measurable_incrMax fun j hj => hf j (hj.trans k.le_succ)
  have hc : Measurable (clipFactor f k) := measurable_const.min (hD.div hi.norm)
  exact hc.smul hi

theorem integrable_clipInc [IsFiniteMeasure μ] (hm : ∀ j, Measurable (f j))
    (hi : ∀ j, Integrable (f j) μ) (k : ℕ) : Integrable (clipInc f k) μ := by
  have hd : Integrable (fun ω => ‖incr f k ω‖) μ := ((hi (k + 1)).sub (hi k)).norm
  refine Integrable.mono' hd (measurable_clipInc fun j _ => hm j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_clipInc]
  exact mul_le_of_le_one_left (norm_nonneg _) (clipFactor_le_one k ω)

theorem integrable_incr_sub_clipInc [IsFiniteMeasure μ] (hm : ∀ j, Measurable (f j))
    (hi : ∀ j, Integrable (f j) μ) (k : ℕ) :
    Integrable (fun ω => incr f k ω - clipInc f k ω) μ :=
  ((hi (k + 1)).sub (hi k)).sub (integrable_clipInc hm hi k)

end RCLike

section Decomposition

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

/-- The rest `dh_k = df_k - dg_k` of the increment after clipping. -/
def restInc (f : ℕ → Ω → 𝕜) (k : ℕ) (ω : Ω) : 𝕜 := incr f k ω - clipInc f k ω

theorem norm_restInc (k : ℕ) (ω : Ω) :
    ‖restInc f k ω‖ = incrMax f (k + 1) ω - incrMax f k ω :=
  norm_incr_sub_clipInc k ω

/-- `g - E_k g` is `ℱ (k+1)`-measurable if `g` is. -/
theorem stronglyMeasurable_sub_condExp {k : ℕ} {g : Ω → 𝕜} (hg : StronglyMeasurable[ℱ (k + 1)] g) :
    StronglyMeasurable[ℱ (k + 1)] (g - μ[g | ℱ k]) :=
  hg.sub ((stronglyMeasurable_condExp (m := ℱ k) (μ := μ) (f := g)).mono (ℱ.mono k.le_succ))

/-- `E_k (g - E_k g) = 0`. -/
theorem condExp_sub_condExp_eq_zero [IsFiniteMeasure μ] {k : ℕ} {g : Ω → 𝕜}
    (hg : Integrable g μ) : μ[g - μ[g | ℱ k] | ℱ k] =ᵐ[μ] 0 := by
  have h2 : μ[μ[g | ℱ k] | ℱ k] = μ[g | ℱ k] :=
    condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp integrable_condExp
  filter_upwards [condExp_sub hg integrable_condExp (ℱ k)] with ω h
  simp only [Pi.sub_apply, Pi.zero_apply] at h ⊢
  rw [h, h2]
  simp

/-- `|E_k g| ≤ c` a.e. if `|g| ≤ c`, `c` integrable and `ℱ k`-measurable. -/
theorem norm_condExp_le_of_le [IsFiniteMeasure μ] {k : ℕ} {g : Ω → 𝕜} {c : Ω → ℝ}
    (hg : Integrable g μ) (hc : Integrable c μ) (hcm : StronglyMeasurable[ℱ k] c)
    (h : ∀ ω, ‖g ω‖ ≤ c ω) : ∀ᵐ ω ∂μ, ‖μ[g | ℱ k] ω‖ ≤ c ω := by
  have h1 := norm_condExp_le (μ := μ) (m := ℱ k) g
  have h2 : μ[fun ω => ‖g ω‖ | ℱ k] ≤ᵐ[μ] μ[c | ℱ k] :=
    condExp_mono hg.norm hc (Filter.Eventually.of_forall h)
  have h3 : μ[c | ℱ k] = c := condExp_of_stronglyMeasurable (ℱ.le k) hcm hc
  filter_upwards [h1, h2] with ω h1 h2
  rw [h3] at h2
  exact h1.trans h2

/-- **Davis decomposition** (Zorin-Kranich's notes, Lemma 1.9): every martingale `f` is the sum
`f = f 0 + P + Q` (a.e.) of two martingales `P = f^pred`, `Q = f^bv` starting at `0`, with a
predictable bound on the jumps of `P`, `‖P_{k+1} - P_k‖ ≤ 2 Mdf_{k-1}` (`incrMax f k` is the
`Mdf_{(k+1)-1}` of Zorin-Kranich's notes for the increment `df_{k+1}`), and bounded variation of
`Q`: `E ∑_{k<N} ‖Q_{k+1} - Q_k‖ ≤ 2 E Mdf_{N-1}` for every `N`. -/
theorem davis_decomposition [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) :
    ∃ P Q : ℕ → Ω → 𝕜, Martingale P ℱ μ ∧ Martingale Q ℱ μ ∧ P 0 = 0 ∧ Q 0 = 0 ∧
      (∀ᵐ ω ∂μ, ∀ n, f n ω = f 0 ω + P n ω + Q n ω) ∧
      (∀ᵐ ω ∂μ, ∀ k, ‖incr P k ω‖ ≤ 2 * incrMax f k ω) ∧
      (∀ N, ∫⁻ ω, ∑ k ∈ range N, ‖incr Q k ω‖ₑ ∂μ ≤
        2 * ∫⁻ ω, ENNReal.ofReal (incrMax f N ω) ∂μ) := by
  have hm : ∀ j, Measurable (f j) := fun j =>
    (hf.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl
  have hi := hf.integrable
  have hmℱ : ∀ k, ∀ j ≤ k, Measurable[ℱ k] (f j) := fun k j hj =>
    ((hf.stronglyMeasurable j).mono (ℱ.mono hj)).measurable
  -- strong measurability of the clipped increments
  have hdgm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (clipInc f k) := fun k =>
    (measurable_clipInc (m := ℱ (k + 1)) fun j hj => hmℱ (k + 1) j hj).stronglyMeasurable
  have hdhm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (restInc f k) := fun k =>
    (((hmℱ (k + 1) (k + 1) le_rfl).sub (hmℱ (k + 1) k k.le_succ)).sub
      (measurable_clipInc (m := ℱ (k + 1)) fun j hj => hmℱ (k + 1) j hj)).stronglyMeasurable
  have hdgi : ∀ k, Integrable (clipInc f k) μ := integrable_clipInc hm hi
  have hdhi : ∀ k, Integrable (restInc f k) μ := integrable_incr_sub_clipInc hm hi
  let p : ℕ → Ω → 𝕜 := fun k => clipInc f k - μ[clipInc f k | ℱ k]
  let q : ℕ → Ω → 𝕜 := fun k => restInc f k - μ[restInc f k | ℱ k]
  have hpm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (p k) := fun k =>
    stronglyMeasurable_sub_condExp (hdgm k)
  have hqm : ∀ k, StronglyMeasurable[ℱ (k + 1)] (q k) := fun k =>
    stronglyMeasurable_sub_condExp (hdhm k)
  have hpi : ∀ k, Integrable (p k) μ := fun k => (hdgi k).sub integrable_condExp
  have hqi : ∀ k, Integrable (q k) μ := fun k => (hdhi k).sub integrable_condExp
  have hPmart : Martingale (fun n ω => ∑ k ∈ range n, p k ω) ℱ μ :=
    martingale_partial_sum hpm hpi fun k => condExp_sub_condExp_eq_zero (hdgi k)
  have hQmart : Martingale (fun n ω => ∑ k ∈ range n, q k ω) ℱ μ :=
    martingale_partial_sum hqm hqi fun k => condExp_sub_condExp_eq_zero (hdhi k)
  have hincP : ∀ k, incr (fun n ω => ∑ j ∈ range n, p j ω) k = p k := fun k => by
    funext ω
    simp [incr_apply, Finset.sum_range_succ]
  have hincQ : ∀ k, incr (fun n ω => ∑ j ∈ range n, q j ω) k = q k := fun k => by
    funext ω
    simp [incr_apply, Finset.sum_range_succ]
  refine ⟨_, _, hPmart, hQmart, by funext ω; simp, by funext ω; simp, ?_, ?_, ?_⟩
  · -- f = f 0 + P + Q
    have hpq : ∀ k, ∀ᵐ ω ∂μ, p k ω + q k ω = incr f k ω := by
      intro k
      have h0 := condExp_incr_eq_zero hf k
      have hadd : μ[clipInc f k + restInc f k | ℱ k] =ᵐ[μ]
          μ[clipInc f k | ℱ k] + μ[restInc f k | ℱ k] := condExp_add (hdgi k) (hdhi k) (ℱ k)
      have hsum : clipInc f k + restInc f k = incr f k := by
        funext ω
        simp [restInc]
      rw [hsum] at hadd
      filter_upwards [hadd, h0] with ω h1 h2
      simp only [Pi.add_apply, Pi.zero_apply] at h1 h2
      simp only [p, q, Pi.sub_apply]
      have : μ[clipInc f k | ℱ k] ω + μ[restInc f k | ℱ k] ω = 0 := by rw [← h1, h2]
      have e : clipInc f k ω + restInc f k ω = incr f k ω := by simp [restInc]
      calc clipInc f k ω - μ[clipInc f k | ℱ k] ω + (restInc f k ω - μ[restInc f k | ℱ k] ω)
          = (clipInc f k ω + restInc f k ω) - (μ[clipInc f k | ℱ k] ω +
              μ[restInc f k | ℱ k] ω) := by ring
        _ = incr f k ω := by rw [this, e, sub_zero]
    filter_upwards [ae_all_iff.2 hpq] with ω hω n
    have h1 : f n ω - f 0 ω = ∑ k ∈ range n, incr f k ω := by
      rw [← Finset.sum_range_sub (fun k => f k ω) n]
      rfl
    have h2 : ∑ k ∈ range n, incr f k ω = ∑ k ∈ range n, p k ω + ∑ k ∈ range n, q k ω := by
      rw [← Finset.sum_add_distrib]
      exact (Finset.sum_congr rfl fun k _ => (hω k).symm)
    linear_combination h1 + h2
  · -- jump bound
    have hbd : ∀ k, ∀ᵐ ω ∂μ, ‖incr (fun n ω => ∑ j ∈ range n, p j ω) k ω‖ ≤
        2 * incrMax f k ω := by
      intro k
      have hDm : StronglyMeasurable[ℱ k] (incrMax f k) :=
        (measurable_incrMax (m := ℱ k) fun j hj => hmℱ k j hj).stronglyMeasurable
      have hDi := integrable_incrMax hm hi k
      filter_upwards [norm_condExp_le_of_le (hdgi k) hDi hDm (norm_clipInc_le k)] with ω hω
      rw [hincP k]
      simp only [p, Pi.sub_apply]
      calc ‖clipInc f k ω - μ[clipInc f k | ℱ k] ω‖
          ≤ ‖clipInc f k ω‖ + ‖μ[clipInc f k | ℱ k] ω‖ := norm_sub_le _ _
        _ ≤ incrMax f k ω + incrMax f k ω := add_le_add (norm_clipInc_le k ω) hω
        _ = 2 * incrMax f k ω := by ring
    exact ae_all_iff.2 hbd
  · -- bounded variation
    intro N
    have hstep : ∀ k, ∫⁻ ω, ‖incr (fun n ω => ∑ j ∈ range n, q j ω) k ω‖ₑ ∂μ ≤
        2 * ∫⁻ ω, ENNReal.ofReal (incrMax f (k + 1) ω - incrMax f k ω) ∂μ := by
      intro k
      rw [hincQ k]
      have hrm : Measurable (restInc f k) := by
        have := (measurable_incr hm k).sub (measurable_clipInc (k := k) (m := m0) fun j _ => hm j)
        exact this
      calc ∫⁻ ω, ‖q k ω‖ₑ ∂μ
          ≤ ∫⁻ ω, (‖restInc f k ω‖ₑ + ‖μ[restInc f k | ℱ k] ω‖ₑ) ∂μ :=
            lintegral_mono fun ω => enorm_sub_le
        _ = ∫⁻ ω, ‖restInc f k ω‖ₑ ∂μ + ∫⁻ ω, ‖μ[restInc f k | ℱ k] ω‖ₑ ∂μ :=
            lintegral_add_left hrm.enorm _
        _ ≤ ∫⁻ ω, ‖restInc f k ω‖ₑ ∂μ + ∫⁻ ω, ‖restInc f k ω‖ₑ ∂μ := by
            refine add_le_add le_rfl ?_
            have := eLpNorm_condExp_le_eLpNorm (μ := μ) (m := ℱ k) (restInc f k) (le_refl 1)
            rwa [eLpNorm_one_eq_lintegral_enorm (stronglyMeasurable_condExp.mono (ℱ.le k)
              |>.aestronglyMeasurable), eLpNorm_one_eq_lintegral_enorm hrm.aestronglyMeasurable]
              at this
        _ = 2 * ∫⁻ ω, ENNReal.ofReal (incrMax f (k + 1) ω - incrMax f k ω) ∂μ := by
            rw [← two_mul]
            congr 2
            funext ω
            rw [← norm_restInc k ω, ofReal_norm]
    calc ∫⁻ ω, ∑ k ∈ range N, ‖incr (fun n ω => ∑ j ∈ range n, q j ω) k ω‖ₑ ∂μ
        = ∑ k ∈ range N, ∫⁻ ω, ‖incr (fun n ω => ∑ j ∈ range n, q j ω) k ω‖ₑ ∂μ := by
          refine lintegral_finsetSum _ fun k _ => ?_
          rw [hincQ k]
          exact (((hqm k).mono (ℱ.le _)).measurable).enorm
      _ ≤ ∑ k ∈ range N, 2 * ∫⁻ ω, ENNReal.ofReal (incrMax f (k + 1) ω - incrMax f k ω) ∂μ :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = 2 * ∫⁻ ω, ENNReal.ofReal (incrMax f N ω) ∂μ := by
          rw [← Finset.mul_sum]
          congr 1
          rw [← lintegral_finsetSum]
          · refine lintegral_congr fun ω => ?_
            rw [← ENNReal.ofReal_sum_of_nonneg fun k _ =>
              sub_nonneg.2 (incrMax_mono ω k.le_succ)]
            rw [Finset.sum_range_sub (fun k => incrMax f k ω) N, incrMax_zero, sub_zero]
          · intro k _
            exact ((measurable_incrMax (m := m0) (k := k + 1) fun j _ => hm j).sub
              (measurable_incrMax (m := m0) (k := k) fun j _ => hm j)).ennreal_ofReal

end Decomposition

end PrimeCarleson.Proof.Lepingle
