module

public import PrimeCarleson.Proof.Lepingle.Prob.Basic

/-!
# Doob's weak-type inequality

Source: Zorin-Kranich's notes `lem:Doob-weak` (01-BDG.tex, L40–L49): Lemma 1.4 (L40-L69): for a
submartingale `f ≥ 0`, `λ > 0` and `n`,
`λ μ{Mf_n > λ} ≤ ∫_{Mf_n > λ} f_n dμ`.

The paper's hitting time `τ = inf{k : f_k > λ}` is replaced by its level sets
`{τ = k} = {f_j ≤ λ for j < k, f_k > λ}`, which lie in `ℱ k`; the submartingale property enters
through `Submartingale.setIntegral_le` on `{τ = k}`.  (Mathlib's `maximal_ineq` has the same
statement with `≥` in place of `>`.)

* `doob_weak`: the inequality, in `ℝ≥0∞` (`lintegral` of `ENNReal.ofReal (f n)`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ}

theorem lt_maxUpTo_iff {E : Type*} [NormedAddCommGroup E] {g : ℕ → Ω → E} {n : ℕ} {c : ℝ≥0∞}
    {ω : Ω} : c < maxUpTo g n ω ↔ ∃ k ≤ n, c < ‖g k ω‖ₑ := by
  simp only [maxUpTo, Finset.lt_sup_iff, Finset.mem_range, Nat.lt_add_one_iff]

/-- For a nonnegative real process, `‖f k ω‖ₑ = ofReal (f k ω)`. -/
theorem enorm_eq_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖x‖ₑ = ENNReal.ofReal x := by
  rw [Real.enorm_eq_ofReal hx]

/-- **Doob's weak-type inequality** (Zorin-Kranich's notes, Lemma 1.4; constant `1`):
for a nonnegative submartingale `f`, `λ > 0` and `n`,
`λ μ{Mf_n > λ} ≤ ∫_{Mf_n > λ} f_n dμ`. -/
theorem doob_weak [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (hnn : ∀ n ω, 0 ≤ f n ω)
    {l : ℝ} (hl : 0 < l) (n : ℕ) :
    ENNReal.ofReal l * μ {ω | ENNReal.ofReal l < maxUpTo f n ω} ≤
      ∫⁻ ω in {ω | ENNReal.ofReal l < maxUpTo f n ω}, ENNReal.ofReal (f n ω) ∂μ := by
  -- the level sets of the hitting time
  let A : ℕ → Set Ω := fun k => {ω | (∀ j < k, f j ω ≤ l) ∧ l < f k ω}
  have hAmeas : ∀ k, MeasurableSet[ℱ k] (A k) := by
    intro k
    have hm : ∀ j ≤ k, Measurable[ℱ k] (f j) := fun j hj =>
      ((hf.stronglyAdapted j).mono (ℱ.mono hj)).measurable
    have : A k = (⋂ j ∈ Finset.range k, {ω | f j ω ≤ l}) ∩ {ω | l < f k ω} := by
      ext ω
      simp [A]
    rw [this]
    refine MeasurableSet.inter ?_ (measurableSet_lt measurable_const (hm k le_rfl))
    refine Finset.measurableSet_biInter _ fun j hj => ?_
    exact measurableSet_le (hm j (Nat.lt_succ_iff.1 (Nat.lt_succ_of_lt (mem_range.1 hj))))
      measurable_const
  have hAm : ∀ k, MeasurableSet (A k) := fun k => ℱ.le k _ (hAmeas k)
  have hdisj : PairwiseDisjoint (↑(Finset.range (n + 1)) : Set ℕ) A := by
    intro s _ t _ hst
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hst with h | h
    · exact absurd (h3 s h) (not_le.2 h2)
    · exact absurd (h1 t h) (not_le.2 h4)
  have hunion : {ω | ENNReal.ofReal l < maxUpTo f n ω} = ⋃ k ∈ Finset.range (n + 1), A k := by
    ext ω
    simp only [mem_ofPred_eq, lt_maxUpTo_iff, mem_iUnion, Finset.mem_range, Nat.lt_add_one_iff,
      exists_prop]
    constructor
    · rintro ⟨k, hk, h⟩
      have hk' : l < f k ω := by
        rw [enorm_eq_ofReal_of_nonneg (hnn k ω)] at h
        by_contra hcon
        exact absurd h (not_lt.2 (ENNReal.ofReal_le_ofReal (not_lt.1 hcon)))
      classical
      have hex : ∃ k, l < f k ω := ⟨k, hk'⟩
      refine ⟨Nat.find hex, (Nat.find_min' hex hk').trans hk, ?_, Nat.find_spec hex⟩
      intro j hj
      exact not_lt.1 (Nat.find_min hex hj)
    · rintro ⟨k, hk, _, h2⟩
      refine ⟨k, hk, ?_⟩
      rw [enorm_eq_ofReal_of_nonneg (hnn k ω)]
      exact (ENNReal.ofReal_lt_ofReal_iff (hl.trans h2)).2 h2
  rw [hunion, measure_biUnion_finset hdisj fun k _ => hAm k, Finset.mul_sum,
    lintegral_biUnion_finset hdisj fun k _ => hAm k]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hint : ∀ j, Integrable (f j) μ := hf.integrable
  calc ENNReal.ofReal l * μ (A k)
      = ∫⁻ ω in A k, ENNReal.ofReal l ∂μ := by rw [setLIntegral_const]
    _ ≤ ∫⁻ ω in A k, ENNReal.ofReal (f k ω) ∂μ :=
        setLIntegral_mono' (hAm k) fun ω hω => ENNReal.ofReal_le_ofReal hω.2.le
    _ = ENNReal.ofReal (∫ ω in A k, f k ω ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint k).integrableOn
          (Filter.Eventually.of_forall fun ω => hnn k ω)]
    _ ≤ ENNReal.ofReal (∫ ω in A k, f n ω ∂μ) :=
        ENNReal.ofReal_le_ofReal (hf.setIntegral_le hkn (hAmeas k))
    _ = ∫⁻ ω in A k, ENNReal.ofReal (f n ω) ∂μ := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint n).integrableOn
          (Filter.Eventually.of_forall fun ω => hnn n ω)]

end PrimeCarleson.Proof.Lepingle
