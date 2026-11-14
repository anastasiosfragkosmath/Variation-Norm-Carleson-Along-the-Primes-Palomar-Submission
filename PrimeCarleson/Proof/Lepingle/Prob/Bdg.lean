module

public import PrimeCarleson.Proof.Lepingle.Prob.Davis
public import PrimeCarleson.Proof.Lepingle.Prob.GarsiaNeveuCor

/-!
# BDG: `‖Sf‖_p ≤ 56 p ‖Mf‖_p`

Source: Zorin-Kranich's notes `cor:BDG` (01-BDG.tex, L443–L449): the direction
`‖Sf‖_p ≲ ‖Mf‖_p` of Corollary 1.13 (L443-L467), `1 ≤ p < ∞`, for a martingale with `f_0 = 0`;
the source only says that this direction is "similar" to the one it proves, so the derivation
given here (through the conditional Davis passage below) is supplied.

* `tailTransform f t B`: the martingale `1_B (f - f^{(t)})` for `B ∈ ℱ t`, as the transform
  `n ↦ ∑_{k<n} 1_{B ∩ {t ≤ k}} (f_{k+1} - f_k)` (`martingale_tailTransform`);
* `lintegral_tail_davis`: Davis' inequality (`lintegral_sqFn_le_davis`) for `1_B (f - f^{(t)})`:
  `E S(1_B(f - f^{(t)})) ≤ 54 E_B Mf`;
* `lintegral_sqFn_sub_le`: the conditional Davis passage
  (`E_t(Sf - Sf_{t-1}) ≤ 56 E_t Mf` in integrated form `∫_B`, `B ∈ ℱ t`);
* `bdg_sqFn_le`: for a martingale `f` and `1 ≤ p < ∞`
  `(∫⁻ (Sf)^p)^{1/p} ≤ 56 p (∫⁻ (Mf)^p)^{1/p}`, via `garsia_neveu_cor` with `A_t = Sf_{t-1}`
  and `ξ = 56 Mf`.  The notes assume `f_0 = 0`; this hypothesis is not needed here (see the
  docstring), so the statement is for every martingale.

No integrability hypothesis is needed (all quantities are `ℝ≥0∞`-valued; if `‖Mf‖_p = ∞` the
inequality is trivial).  The constant `C_D = 27` of Davis' inequality gives
`C_p = p (2 + 2 C_D) = 56 p`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

section Split

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E]

/-- Splitting the square function at a time `a ≤ n`: if `‖df_k‖ ≤ ‖dg_k‖` for `a ≤ k < n`, then
`S f_n ≤ S f_a + S g_n` (Minkowski in `ℓ²`). -/
theorem sqUpTo_le_add_tail {f g : ℕ → Ω → E} {a n : ℕ} {ω : Ω} (han : a ≤ n)
    (h : ∀ k, a ≤ k → k < n → ‖incr f k ω‖ₑ ≤ ‖incr g k ω‖ₑ) :
    sqUpTo f n ω ≤ sqUpTo f a ω + sqUpTo g n ω := by
  set u : ℕ → ℝ≥0∞ := fun k => if k < a then ‖incr f k ω‖ₑ else 0 with hu
  have h1 : ∀ k ∈ range n, ‖incr f k ω‖ₑ ≤ u k + ‖incr g k ω‖ₑ := by
    intro k hk
    by_cases hka : k < a
    · simp [hu, hka]
    · simp only [hu, hka, ite_false, zero_add]
      exact h k (not_lt.1 hka) (Finset.mem_range.1 hk)
  have h2 : ∑ k ∈ range n, u k ^ (2 : ℝ) = ∑ k ∈ range a, ‖incr f k ω‖ₑ ^ (2 : ℝ) := by
    rw [← Finset.sum_subset (Finset.range_mono han) ?_]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [hu, Finset.mem_range.1 hk]
    · intro k _ hk
      have : ¬ k < a := fun h => hk (Finset.mem_range.2 h)
      simp [hu, this, ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 2 by norm_num)]
  calc sqUpTo f n ω = (∑ k ∈ range n, ‖incr f k ω‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := rfl
    _ ≤ (∑ k ∈ range n, (u k + ‖incr g k ω‖ₑ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum fun k hk =>
          ENNReal.rpow_le_rpow (h1 k hk) (by norm_num)) (by norm_num)
    _ ≤ (∑ k ∈ range n, u k ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
          (∑ k ∈ range n, ‖incr g k ω‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.Lp_add_le _ _ _ (by norm_num)
    _ = sqUpTo f a ω + sqUpTo g n ω := by rw [h2]; rfl

/-- `S f_{s+1} ≤ S f_s + ‖df_{s+1}‖`. -/
theorem sqUpTo_succ_le (f : ℕ → Ω → E) (s : ℕ) (ω : Ω) :
    sqUpTo f (s + 1) ω ≤ sqUpTo f s ω + ‖incr f s ω‖ₑ := by
  unfold sqUpTo
  rw [Finset.sum_range_succ]
  refine (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans ?_
  rw [← ENNReal.rpow_mul]
  norm_num

end Split

section Roots

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Homogeneity of the `L^p` seminorm in `ℝ≥0∞`: if `g ≤ c h` pointwise, `c < ∞`, `p > 0`, then
`(∫ g^p)^{1/p} ≤ c (∫ h^p)^{1/p}`. -/
theorem root_lintegral_le_const_mul {g h : Ω → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ∞) {p : ℝ} (hp : 0 < p) (hgh : ∀ ω, g ω ≤ c * h ω) :
    (∫⁻ ω, g ω ^ p ∂μ) ^ (1 / p) ≤ c * (∫⁻ ω, h ω ^ p ∂μ) ^ (1 / p) := by
  have h1 : ∫⁻ ω, g ω ^ p ∂μ ≤ c ^ p * ∫⁻ ω, h ω ^ p ∂μ := by
    calc ∫⁻ ω, g ω ^ p ∂μ ≤ ∫⁻ ω, c ^ p * h ω ^ p ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          exact ENNReal.rpow_le_rpow (hgh ω) hp.le
      _ = c ^ p * ∫⁻ ω, h ω ^ p ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le hc)
  calc (∫⁻ ω, g ω ^ p ∂μ) ^ (1 / p) ≤ (c ^ p * ∫⁻ ω, h ω ^ p ∂μ) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h1 (by positivity)
    _ = c * (∫⁻ ω, h ω ^ p ∂μ) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end Roots

section Tail

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

/-- The set `B ∩ {t ≤ k}`: the event `B` from time `t` on. -/
def tailSet (t : ℕ) (B : Set Ω) (k : ℕ) : Set Ω := {ω | t ≤ k ∧ ω ∈ B}

theorem measurableSet_tailSet {t : ℕ} {B : Set Ω} (hB : MeasurableSet[ℱ t] B) (k : ℕ) :
    MeasurableSet[ℱ k] (tailSet t B k) := by
  by_cases h : t ≤ k
  · have : tailSet t B k = B := by
      ext ω
      simp [tailSet, h]
    rw [this]
    exact ℱ.mono h _ hB
  · have : tailSet t B k = ∅ := by
      ext ω
      simp [tailSet, h]
    rw [this]
    exact @MeasurableSet.empty _ (ℱ k)

/-- The martingale `1_B (f - f^{(t)})` for `B ∈ ℱ t`, written as the transform
`n ↦ ∑_{k<n} 1_{B ∩ {t ≤ k}} (f_{k+1} - f_k)`; it equals `1_B (f_{max(n,t)} - f_t)`
(`tailTransform_of_mem`). -/
def tailTransform (f : ℕ → Ω → 𝕜) (t : ℕ) (B : Set Ω) (n : ℕ) (ω : Ω) : 𝕜 :=
  ∑ k ∈ range n, (tailSet t B k).indicator (incr f k) ω

theorem martingale_tailTransform [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {t : ℕ}
    {B : Set Ω} (hB : MeasurableSet[ℱ t] B) : Martingale (tailTransform f t B) ℱ μ :=
  martingale_indicator_incr hf (measurableSet_tailSet hB)

theorem tailTransform_zero (f : ℕ → Ω → 𝕜) (t : ℕ) (B : Set Ω) :
    tailTransform f t B 0 = 0 := by
  funext ω
  simp [tailTransform]

theorem incr_tailTransform (f : ℕ → Ω → 𝕜) (t : ℕ) (B : Set Ω) (k : ℕ) (ω : Ω) :
    incr (tailTransform f t B) k ω = (tailSet t B k).indicator (incr f k) ω := by
  simp [incr_apply, tailTransform, Finset.sum_range_succ]

theorem tailTransform_of_notMem {t : ℕ} {B : Set Ω} {ω : Ω} (hω : ω ∉ B) (n : ℕ) :
    tailTransform f t B n ω = 0 := by
  unfold tailTransform
  refine Finset.sum_eq_zero fun k _ => ?_
  exact Set.indicator_of_notMem (fun h => hω h.2) _

theorem tailTransform_of_mem {t : ℕ} {B : Set Ω} {ω : Ω} (hω : ω ∈ B) (n : ℕ) :
    tailTransform f t B n ω = f (max n t) ω - f t ω := by
  induction n with
  | zero => simp [tailTransform]
  | succ n ih =>
    have h1 : tailTransform f t B (n + 1) ω =
        tailTransform f t B n ω + (tailSet t B n).indicator (incr f n) ω := by
      simp [tailTransform, Finset.sum_range_succ]
    rw [h1, ih]
    by_cases htn : t ≤ n
    · rw [Set.indicator_of_mem (show ω ∈ tailSet t B n from ⟨htn, hω⟩), incr_apply,
        max_eq_left htn, max_eq_left (htn.trans n.le_succ)]
      ring
    · have hn : n < t := not_le.1 htn
      rw [Set.indicator_of_notMem (fun h => htn h.1), max_eq_right hn.le,
        max_eq_right (Nat.succ_le_of_lt hn)]
      simp

theorem enorm_tailTransform_le (t : ℕ) (B : Set Ω) (n : ℕ) (ω : Ω) :
    ‖tailTransform f t B n ω‖ₑ ≤ B.indicator (fun ω => 2 * maxFn f ω) ω := by
  by_cases hω : ω ∈ B
  · rw [Set.indicator_of_mem hω, tailTransform_of_mem hω]
    calc ‖f (max n t) ω - f t ω‖ₑ ≤ ‖f (max n t) ω‖ₑ + ‖f t ω‖ₑ := enorm_sub_le
      _ ≤ maxFn f ω + maxFn f ω := add_le_add (le_maxFn _) (le_maxFn _)
      _ = 2 * maxFn f ω := (two_mul _).symm
  · rw [Set.indicator_of_notMem hω, tailTransform_of_notMem hω]
    simp

theorem maxFn_tailTransform_le (t : ℕ) (B : Set Ω) (ω : Ω) :
    maxFn (tailTransform f t B) ω ≤ B.indicator (fun ω => 2 * maxFn f ω) ω :=
  maxFn_le_iff.2 fun n => enorm_tailTransform_le t B n ω

/-- **Davis' inequality for `1_B (f - f^{(t)})`**, `B ∈ ℱ t` (Zorin-Kranich's notes, L451-L456):
`E S(1_B (f - f^{(t)})) ≤ 54 E_B Mf`. -/
theorem lintegral_tail_davis [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {t : ℕ} {B : Set Ω}
    (hB : MeasurableSet[ℱ t] B) :
    ∫⁻ ω, sqFn (tailTransform f t B) ω ∂μ ≤ 54 * ∫⁻ ω in B, maxFn f ω ∂μ := by
  have hBm : MeasurableSet B := ℱ.le t _ hB
  have hm : ∀ j, Measurable (f j) := fun j =>
    (hf.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl
  refine (lintegral_sqFn_le_davis (martingale_tailTransform hf hB)
    (tailTransform_zero f t B)).trans ?_
  calc 27 * ∫⁻ ω, maxFn (tailTransform f t B) ω ∂μ
      ≤ 27 * ∫⁻ ω, B.indicator (fun ω => 2 * maxFn f ω) ω ∂μ :=
        mul_le_mul_right (lintegral_mono fun ω => maxFn_tailTransform_le t B ω) _
    _ = 27 * (2 * ∫⁻ ω in B, maxFn f ω ∂μ) := by
        rw [lintegral_indicator hBm, lintegral_const_mul _ (measurable_maxFn hm)]
    _ = 54 * ∫⁻ ω in B, maxFn f ω ∂μ := by ring

/-- **The conditional Davis passage**: for `B ∈ ℱ (s+1)`,
`∫_B (Sf - Sf_s) ≤ 56 ∫_B Mf` (`Sf_s = sqUpTo f s`, the square function of the first `s`
increments; `A_{s+1} = Sf_s` is the predictable process of the Garsia-Neveu step). -/
theorem lintegral_sqFn_sub_le [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) (s : ℕ) {B : Set Ω}
    (hB : MeasurableSet[ℱ (s + 1)] B) :
    ∫⁻ ω in B, (sqFn f ω - sqUpTo f s ω) ∂μ ≤ 56 * ∫⁻ ω in B, maxFn f ω ∂μ := by
  have hBm : MeasurableSet B := ℱ.le _ _ hB
  have hm : ∀ j, Measurable (f j) := fun j =>
    (hf.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl
  set T := tailTransform f (s + 1) B with hT
  -- pointwise comparison on `B`
  have hpt : ∀ ω ∈ B, sqFn f ω - sqUpTo f s ω ≤ ‖incr f s ω‖ₑ + sqFn T ω := by
    intro ω hω
    rw [tsub_le_iff_left]
    refine sqFn_le_iff.2 fun n => ?_
    have hmem : ∀ k, s + 1 ≤ k → ‖incr f k ω‖ₑ ≤ ‖incr T k ω‖ₑ := by
      intro k hk
      rw [hT, incr_tailTransform, Set.indicator_of_mem (show ω ∈ tailSet (s + 1) B k from ⟨hk, hω⟩)]
    calc sqUpTo f n ω ≤ sqUpTo f (max n (s + 1)) ω := sqUpTo_mono (le_max_left _ _)
      _ ≤ sqUpTo f (s + 1) ω + sqUpTo T (max n (s + 1)) ω :=
          sqUpTo_le_add_tail (le_max_right _ _) fun k hk _ => hmem k hk
      _ ≤ (sqUpTo f s ω + ‖incr f s ω‖ₑ) + sqFn T ω :=
          add_le_add (sqUpTo_succ_le f s ω) (sqUpTo_le_sqFn _)
      _ = sqUpTo f s ω + (‖incr f s ω‖ₑ + sqFn T ω) := add_assoc _ _ _
  have hincr : Measurable fun ω => ‖incr f s ω‖ₑ := (measurable_incr hm s).enorm
  calc ∫⁻ ω in B, (sqFn f ω - sqUpTo f s ω) ∂μ
      ≤ ∫⁻ ω in B, (‖incr f s ω‖ₑ + sqFn T ω) ∂μ := setLIntegral_mono' hBm hpt
    _ = ∫⁻ ω in B, ‖incr f s ω‖ₑ ∂μ + ∫⁻ ω in B, sqFn T ω ∂μ := lintegral_add_left hincr _
    _ ≤ 2 * ∫⁻ ω in B, maxFn f ω ∂μ + 54 * ∫⁻ ω in B, maxFn f ω ∂μ := by
        refine add_le_add ?_ ?_
        · calc ∫⁻ ω in B, ‖incr f s ω‖ₑ ∂μ ≤ ∫⁻ ω in B, 2 * maxFn f ω ∂μ :=
              lintegral_mono fun ω => enorm_incr_le_two_mul_maxFn s
            _ = 2 * ∫⁻ ω in B, maxFn f ω ∂μ :=
              lintegral_const_mul _ (measurable_maxFn hm)
        · exact (setLIntegral_le_lintegral _ _).trans (lintegral_tail_davis hf hB)
    _ = 56 * ∫⁻ ω in B, maxFn f ω ∂μ := by ring

end Tail

section BDG

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

theorem iSup_sqUpTo_pred (f : ℕ → Ω → 𝕜) (ω : Ω) :
    (⨆ s, sqUpTo f (s - 1) ω) = sqFn f ω := by
  refine le_antisymm (iSup_le fun s => sqUpTo_le_sqFn _) (iSup_le fun n => ?_)
  exact le_iSup_of_le (n + 1) (by simp)

/-- **BDG, direction `‖Sf‖_p ≲ ‖Mf‖_p`** (Zorin-Kranich's notes, Corollary 1.13): for a
martingale `f` and `1 ≤ p < ∞`, `‖Sf‖_p ≤ 56 p ‖Mf‖_p`, in
`ℝ≥0∞` and `lintegral` form, with `Sf = (∑_{k≥1} ‖f_k - f_{k-1}‖²)^{1/2}` (the square function of
the increments, `sqFn f`) and `Mf = sup_n ‖f_n‖` (`maxFn f`).  The hypothesis `f_0 = 0` of the
notes is not needed (it is only used for the *tails* `1_B (f - f^{(t)})`, which start at `0` by
construction; `‖df_t‖ ≤ 2 Mf` absorbs the first increment), and no integrability hypothesis is
needed (the right side may be `∞`). -/
theorem bdg_sqFn_le [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {p : ℝ}
    (hp : 1 ≤ p) :
    (∫⁻ ω, sqFn f ω ^ p ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal (56 * p) * (∫⁻ ω, maxFn f ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hm : ∀ j, Measurable (f j) := fun j =>
    (hf.stronglyMeasurable j).measurable.mono (ℱ.le j) le_rfl
  have hmℱ : ∀ k, ∀ j ≤ k, Measurable[ℱ k] (f j) := fun k j hj =>
    ((hf.stronglyMeasurable j).mono (ℱ.mono hj)).measurable
  let A : ℕ → Ω → ℝ≥0∞ := fun s ω => sqUpTo f (s - 1) ω
  have hA0 : A 0 = 0 := by
    funext ω
    simp [A, sqUpTo_zero]
  have hmono : ∀ ω, Monotone fun t => A t ω := fun ω a b hab =>
    sqUpTo_mono (Nat.sub_le_sub_right hab 1)
  have hpred : ∀ t, Measurable[ℱ t] (A (t + 1)) := fun t =>
    measurable_sqUpTo (m := ℱ t) fun k hk => hmℱ t k hk
  have hsup : ∀ ω, (⨆ s, A s ω) = sqFn f ω := iSup_sqUpTo_pred f
  have hξ : Measurable fun ω => (56 : ℝ≥0∞) * maxFn f ω :=
    (measurable_maxFn hm).const_mul _
  have h : ∀ t : ℕ, ∀ B : Set Ω, MeasurableSet[ℱ t] B →
      ∫⁻ ω in B, ((⨆ s, A s ω) - A t ω) ∂μ ≤ ∫⁻ ω in B, (56 : ℝ≥0∞) * maxFn f ω ∂μ := by
    intro t B hB
    rw [lintegral_const_mul _ (measurable_maxFn hm)]
    simp_rw [hsup]
    rcases t with _ | s
    · have h1 := lintegral_sqFn_sub_le hf 0 (ℱ.mono (Nat.zero_le 1) _ hB)
      have hA : A 0 = fun ω => sqUpTo f 0 ω := by
        funext ω
        simp [A]
      rw [hA]
      exact h1
    · have : A (s + 1) = fun ω => sqUpTo f s ω := by
        funext ω
        simp [A]
      rw [this]
      exact lintegral_sqFn_sub_le hf s hB
  have hGN := garsia_neveu_cor ℱ hA0 hmono hpred hξ h hp
  simp_rw [hsup] at hGN
  have hξp := root_lintegral_le_const_mul (μ := μ) (g := fun ω => (56 : ℝ≥0∞) * maxFn f ω)
    (h := maxFn f) (c := 56) (by norm_num) hp0 fun ω => le_rfl
  have hofReal : ENNReal.ofReal (56 * p) = 56 * ENNReal.ofReal p := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  calc (∫⁻ ω, sqFn f ω ^ p ∂μ) ^ (1 / p)
      ≤ ENNReal.ofReal p * (∫⁻ ω, ((56 : ℝ≥0∞) * maxFn f ω) ^ p ∂μ) ^ (1 / p) := hGN
    _ ≤ ENNReal.ofReal p * (56 * (∫⁻ ω, maxFn f ω ^ p ∂μ) ^ (1 / p)) := by gcongr
    _ = ENNReal.ofReal (56 * p) * (∫⁻ ω, maxFn f ω ^ p ∂μ) ^ (1 / p) := by
        rw [hofReal]
        ring

end BDG

end PrimeCarleson.Proof.Lepingle
