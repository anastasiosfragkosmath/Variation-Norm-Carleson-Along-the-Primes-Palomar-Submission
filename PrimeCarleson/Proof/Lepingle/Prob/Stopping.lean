module

public import PrimeCarleson.Proof.Lepingle.Prob.Bdg
public import PrimeCarleson.Proof.Lepingle.Path.Square

/-!
# The oscillation partition as stopping times; optional sampling

Source: Zorin-Kranich's notes `eq:stop-times` (02-Lepingle.tex, L35–L41) (the adaptedness half; the
pathwise half is `Lepingle/Path/StoppingTimes.lean`), together with the optional sampling theorem
and the calculus of stopping times (both taken from Mathlib); see also 02-Lepingle.tex L34-L41,
L139.

For a process `f : ℕ → Ω → 𝕜` on a filtered space `(Ω, ℱ)` and a horizon `N`:

* `partTime f N m j ω = sampleTime (n ↦ f n ω) N m j = τ^{(m)}_j(ω) ∧ N` (the bounded version of
  the time of Zorin-Kranich's notes, with the convention `f_∞ := f_N`);
* `isStoppingTime_partStop`: `ω ↦ τ^{(m)}_j(ω) ∧ N` is a stopping time for `ℱ` (induction on `j`,
  from the pathwise recursion `sampleTime_succ_le_iff`: the rule at time `t` reads only
  `f 0, …, f t`);
* `sampled f N m j = f_{τ^{(m)}_j ∧ N}` and the filtration `𝒢_j = ℱ_{τ^{(m)}_j ∧ N}`
  (`partFiltration`);
* `martingale_sampled`: for a martingale `f`,
  `(f_{τ_j ∧ N})_j` is a martingale for `(ℱ_{τ_j ∧ N})_j` (Mathlib's optional sampling theorem
  `Martingale.stoppedValue_ae_eq_condExp_of_le` for the bounded stopping times
  `τ_j ∧ N ≤ τ_{j+1} ∧ N ≤ N`).

No "constant after `N`" hypothesis is needed: the horizon `N` is explicit, and the pathwise
bound of `Lepingle/Path` is for the path on `[0, N]`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {𝕜 : Type*} [RCLike 𝕜] {f : ℕ → Ω → 𝕜}

/-- The time `τ^{(m)}_j ∧ N` of the path `n ↦ f n ω`, as a natural number. -/
def partTime (f : ℕ → Ω → 𝕜) (N m j : ℕ) (ω : Ω) : ℕ := sampleTime (fun n => f n ω) N m j

theorem partTime_le (f : ℕ → Ω → 𝕜) (N m j : ℕ) (ω : Ω) : partTime f N m j ω ≤ N :=
  sampleTime_le _ N m j

theorem partTime_zero (f : ℕ → Ω → 𝕜) (N m : ℕ) (ω : Ω) : partTime f N m 0 ω = 0 :=
  sampleTime_zero _ N m

theorem partTime_mono (f : ℕ → Ω → 𝕜) (N m : ℕ) (ω : Ω) :
    Monotone fun j => partTime f N m j ω :=
  monotone_nat_of_le_succ fun j => sampleTime_le_succ _ N m j

/-- The stopping rule `StopRule (n ↦ f n ω) m s t` is an `ℱ t`-measurable event
(it only reads `f 0, …, f t`). -/
theorem measurableSet_stopRule (hf : StronglyAdapted ℱ f) (m s t : ℕ) :
    MeasurableSet[ℱ t] {ω | StopRule (fun n => f n ω) m s t} := by
  let _ : MeasurableSpace Ω := ℱ t
  have hm : ∀ a ≤ t, StronglyMeasurable (f a) := fun a ha => (hf a).mono (ℱ.mono ha)
  have hd : ∀ a ≤ t, ∀ b ≤ t, Measurable fun ω => dist (f a ω) (f b ω) := fun a ha b hb =>
    ((hm a ha).dist (hm b hb)).measurable
  have hosc : Measurable fun ω => runningOsc (fun n => f n ω) t := by
    have h := Finset.measurable_sup' (δ := Ω)
      (s := Finset.range (t + 1) ×ˢ Finset.range (t + 1)) ⟨(0, 0), by simp⟩
      (f := fun (p : ℕ × ℕ) ω => dist (f p.1 ω) (f p.2 ω)) fun p hp => by
        simp only [Finset.mem_product, Finset.mem_range] at hp
        exact hd p.1 (by omega) p.2 (by omega)
    convert h using 1
    funext ω
    simp only [runningOsc]
    exact (Finset.sup'_apply (C := fun _ : Ω => ℝ) (⟨(0, 0), by simp⟩ :
      (Finset.range (t + 1) ×ˢ Finset.range (t + 1)).Nonempty)
      (fun (p : ℕ × ℕ) ω => dist (f p.1 ω) (f p.2 ω)) ω).symm
  by_cases hst : s ≤ t
  · have : {ω | StopRule (fun n => f n ω) m s t} =
        {ω | 0 < runningOsc (fun n => f n ω) t} ∩
          {ω | (2⁻¹ : ℝ) ^ m * runningOsc (fun n => f n ω) t ≤ dist (f t ω) (f s ω)} := by
      ext ω
      simp [StopRule, hst]
    rw [this]
    exact (measurableSet_lt measurable_const hosc).inter
      (measurableSet_le (hosc.const_mul _) (hd t le_rfl s hst))
  · have : {ω | StopRule (fun n => f n ω) m s t} = ∅ := by
      ext ω
      simp [StopRule, hst]
    rw [this]
    exact MeasurableSet.empty

/-- The time `τ^{(m)}_j ∧ N` as a `WithTop ℕ`-valued function (the type of Mathlib's stopping
times). -/
def partStop (f : ℕ → Ω → 𝕜) (N m j : ℕ) (ω : Ω) : WithTop ℕ :=
  WithTop.some (partTime f N m j ω)

/-- **The times `τ^{(m)}_j ∧ N` are stopping times** (Zorin-Kranich's notes, L139 and
the Claim at L63): for an adapted process `f` and every `j`, `ω ↦ τ^{(m)}_j(ω) ∧ N` is an
`ℱ`-stopping time, bounded by `N`. -/
theorem isStoppingTime_partStop (hf : StronglyAdapted ℱ f) (N m j : ℕ) :
    IsStoppingTime ℱ (partStop f N m j) := by
  induction j with
  | zero =>
    have : partStop f N m 0 = fun _ => WithTop.some (0 : ℕ) := by
      funext ω
      simp only [partStop, partTime_zero]
    rw [this]
    exact isStoppingTime_const ℱ 0
  | succ j ih =>
    intro n
    by_cases hn : n < N
    · have hset : {ω | partStop f N m (j + 1) ω ≤ WithTop.some n} =
          ⋃ s ∈ Finset.range (n + 1), ⋃ t ∈ Finset.range (n + 1),
            {ω | partTime f N m j ω = s} ∩ {ω | StopRule (fun k => f k ω) m s t} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff,
          exists_prop, partStop, WithTop.coe_le_coe]
        rw [partTime, sampleTime_succ_le_iff hn]
        constructor
        · rintro ⟨s, t, htn, hs, hr⟩
          exact ⟨s, by have := hr.1; omega, t, by omega, hs, hr⟩
        · rintro ⟨s, _, t, ht, hs, hr⟩
          exact ⟨s, t, by omega, hs, hr⟩
      change MeasurableSet[ℱ n] {ω | partStop f N m (j + 1) ω ≤ WithTop.some n}
      rw [hset]
      refine Finset.measurableSet_biUnion _ fun s hs =>
        Finset.measurableSet_biUnion _ fun t ht => ?_
      have hs' : s ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
      have ht' : t ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
      refine MeasurableSet.inter ?_ ?_
      · have := ih.measurableSet_eq_of_countable s
        have h2 : {ω | partStop f N m j ω = WithTop.some s} = {ω | partTime f N m j ω = s} := by
          ext ω
          simp [partStop]
        rw [h2] at this
        exact ℱ.mono hs' _ this
      · exact ℱ.mono ht' _ (measurableSet_stopRule hf m s t)
    · have : {ω | partStop f N m (j + 1) ω ≤ WithTop.some n} = Set.univ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, partStop, WithTop.coe_le_coe]
        exact (partTime_le f N m (j + 1) ω).trans (not_lt.1 hn)
      change MeasurableSet[ℱ n] {ω | partStop f N m (j + 1) ω ≤ WithTop.some n}
      rw [this]
      exact @MeasurableSet.univ _ (ℱ n)

/-- The sampled sequence `j ↦ f_{τ^{(m)}_j ∧ N}` (Zorin-Kranich's notes, L139-L144). -/
def sampled (f : ℕ → Ω → 𝕜) (N m j : ℕ) (ω : Ω) : 𝕜 := f (partTime f N m j ω) ω

theorem sampled_eq_stoppedValue (f : ℕ → Ω → 𝕜) (N m j : ℕ) :
    sampled f N m j = stoppedValue f (partStop f N m j) := by
  funext ω
  rfl

/-- The filtration `j ↦ ℱ_{τ^{(m)}_j ∧ N}` of the sampled sequence (the `σ`-algebras of the
stopping times of `isStoppingTime_partStop`; they increase since the times do). -/
def partFiltration (hf : StronglyAdapted ℱ f) (N m : ℕ) : Filtration ℕ m0 where
  seq j := (isStoppingTime_partStop hf N m j).measurableSpace
  mono' := by
    refine monotone_nat_of_le_succ fun j => IsStoppingTime.measurableSpace_mono _ _ ?_
    intro ω
    exact WithTop.coe_le_coe.2 (partTime_mono f N m ω (Nat.le_succ j))
  le' j := (isStoppingTime_partStop hf N m j).measurableSpace_le

/-- **Optional sampling for the oscillation partition** (Zorin-Kranich's notes, L139): for a
martingale `f`, the sampled sequence `(f_{τ^{(m)}_j ∧ N})_j` is a martingale for the filtration
`(ℱ_{τ^{(m)}_j ∧ N})_j`.  (Mathlib's optional sampling theorem for the bounded stopping times
`τ_i ∧ N ≤ τ_j ∧ N ≤ N`; integrability of `f_{τ_j ∧ N}` is the one of a stopped value at a bounded
time.) -/
theorem martingale_sampled [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) (N m : ℕ) :
    Martingale (sampled f N m) (partFiltration hf.stronglyAdapted N m) μ := by
  have hτ := isStoppingTime_partStop hf.stronglyAdapted N m
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · have hprog := hf.stronglyAdapted.isStronglyProgressive_of_discrete
    have := measurable_stoppedValue hprog (hτ j)
    rw [sampled_eq_stoppedValue]
    exact this.stronglyMeasurable
  · have hle : partStop f N m i ≤ partStop f N m j := fun ω =>
      WithTop.coe_le_coe.2 (partTime_mono f N m ω hij)
    have hbdd : ∀ ω, partStop f N m j ω ≤ (N : WithTop ℕ) := fun ω =>
      WithTop.coe_le_coe.2 (partTime_le f N m j ω)
    have := hf.stoppedValue_ae_eq_condExp_of_le (hτ j) (hτ i) hle hbdd
    rw [sampled_eq_stoppedValue, sampled_eq_stoppedValue]
    exact this.symm

/-- The square function `S_{(m)}` of the path (`sqFun`) is the square function of the sampled
sequence `sampled f N m`, up to time `N`. -/
theorem sqFun_eq_sqUpTo_sampled (f : ℕ → Ω → 𝕜) (N m : ℕ) (ω : Ω) :
    sqFun (fun n => f n ω) N m = sqUpTo (sampled f N m) N ω := by
  unfold sqFun sqUpTo
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ENNReal.rpow_two]
  congr 1
  unfold sampleIncrement
  rw [edist_eq_enorm_sub, enorm_sub_rev]
  rfl

theorem maxFn_sampled_le (f : ℕ → Ω → 𝕜) (N m : ℕ) (ω : Ω) :
    maxFn (sampled f N m) ω ≤ maxUpTo f N ω :=
  maxFn_le_iff.2 fun j => le_maxUpTo (partTime_le f N m j ω)

/-- **BDG for the sampled martingales** (Zorin-Kranich's notes, L159-L163), first form:
`‖S_{(m)}‖_p ≤ 56 p ‖sup_j |f_{τ_j ∧ N}|‖_p` for a martingale `f`, `1 ≤ p < ∞`, any horizon `N`
and level `m`. -/
theorem bdg_stopped_sampled [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {p : ℝ} (hp : 1 ≤ p)
    (N m : ℕ) :
    (∫⁻ ω, sqFun (fun n => f n ω) N m ^ p ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal (56 * p) * (∫⁻ ω, maxFn (sampled f N m) ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hB := bdg_sqFn_le (martingale_sampled hf N m) hp
  refine le_trans ?_ hB
  refine ENNReal.rpow_le_rpow (lintegral_mono fun ω => ?_) (by positivity)
  simp_rw [sqFun_eq_sqUpTo_sampled]
  exact ENNReal.rpow_le_rpow (sqUpTo_le_sqFn N) hp0.le

/-- **BDG for the sampled martingales** (Zorin-Kranich's notes, L159-L165): for a martingale `f`,
`1 ≤ p < ∞`, every horizon `N` and level `m`,
`‖S_{(m)}‖_p ≤ 56 p ‖sup_{k ≤ N} |f_k|‖_p`, with the constant `56 p` independent of `m`, `N`
(the notes ask for `C'_p`, twice the BDG constant, for the version with `f_0` subtracted;
`bdg_sqFn_le` needs no `f_0 = 0`, so the constant is `56 p`). -/
theorem bdg_stopped [IsFiniteMeasure μ] (hf : Martingale f ℱ μ) {p : ℝ} (hp : 1 ≤ p)
    (N m : ℕ) :
    (∫⁻ ω, sqFun (fun n => f n ω) N m ^ p ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal (56 * p) * (∫⁻ ω, maxUpTo f N ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  refine (bdg_stopped_sampled hf hp N m).trans ?_
  gcongr with ω
  exact maxFn_sampled_le f N m ω

end PrimeCarleson.Proof.Lepingle
