module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.SuccPred.ENat

/-!
# The oscillation stopping times of Lépingle's inequality, pathwise

Deterministic (one sample path) part of the proof of Theorem 2.1 of Zorin-Kranich's notes
(02-Lepingle.tex, L31-L168).  Source: Zorin-Kranich's notes `eq:stop-times` (02-Lepingle.tex,
L35–L41).

For a path `f : ℕ → E` in a pseudo-metric space (the proof only uses the triangle inequality;
the martingales of Zorin-Kranich's notes are `ℂ`-valued) we define

* `runningOsc f t = M_t = max_{s, s' ≤ t} dist (f s) (f s')` (display (2.2), L34);
* `StopRule f m s t` : `t ≥ s`, `M_t > 0` and `dist (f t) (f s) ≥ 2^{-m} M_t`;
* `stopTime f m j = τ^{(m)}_j ∈ ℕ∞`: `τ_0 = 0`, `τ_{j+1} = inf {t ≥ τ_j | StopRule f m τ_j t}`
  with `inf ∅ = ∞` (display (2.2), L35-L41);
* `sampleTime f N m j = τ^{(m)}_j ∧ N`, the bounded version used on the horizon `[0, N]`: it is the
  value of `τ^{(m)}_j` of the path stopped at `N` (the notes' convention `f_∞ := f_N`), and the one
  at which the sampled sequence `f_{τ_j ∧ N}` is read.

The deterministic content of the stopping-time claim of the notes is proved here: `τ_0 = 0`
(`stopTime_zero`), `τ_j < τ_{j+1}` while finite (`stopTime_lt_succ`), the rule holds at a
finite `τ_{j+1}` (`stopRule_of_stopTime_succ_eq`), fails strictly between consecutive times
(`not_stopRule_of_lt_stopTime_succ`), and `τ_j ≥ j` (`le_stopTime`). The *adaptedness*
(stopping time property) is stated pathwise as the explicit recursion `stopTime_succ_le_iff` /
`sampleTime_succ_le_iff` (the rule at `t` only reads `f 0, …, f t`):
`{τ_{j+1} ≤ n}` is the union over `s ≤ t ≤ n` of `{τ_j = s} ∩ {StopRule f m s t}`.
The measurability statement itself, `IsStoppingTime`, is a probabilistic claim and is proved in
`Lepingle/Prob/Stopping.lean`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {E : Type*} [PseudoMetricSpace E]

/-! ### The running oscillation -/

/-- The running oscillation `M_t = max_{s, s' ≤ t} dist (f s) (f s')` of a path
(Zorin-Kranich's notes, L34 writes the maximum over `t'' ≤ t' ≤ t`, the same
number by symmetry of the distance). -/
def runningOsc (f : ℕ → E) (t : ℕ) : ℝ :=
  (Finset.range (t + 1) ×ˢ Finset.range (t + 1)).sup' ⟨(0, 0), by simp⟩
    fun p => dist (f p.1) (f p.2)

/-- Every distance between two values up to time `t` is at most `M_t`. -/
theorem dist_le_runningOsc (f : ℕ → E) {s s' t : ℕ} (hs : s ≤ t) (hs' : s' ≤ t) :
    dist (f s) (f s') ≤ runningOsc f t :=
  Finset.le_sup' (fun p : ℕ × ℕ => dist (f p.1) (f p.2)) (b := (s, s'))
    (Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hs),
      Finset.mem_range.2 (Nat.lt_succ_of_le hs')⟩)

/-- `M_t` is attained by a pair of times `≤ t`. -/
theorem exists_dist_eq_runningOsc (f : ℕ → E) (t : ℕ) :
    ∃ s s' : ℕ, s ≤ t ∧ s' ≤ t ∧ dist (f s) (f s') = runningOsc f t := by
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup' (⟨(0, 0), by simp⟩ :
    (Finset.range (t + 1) ×ˢ Finset.range (t + 1)).Nonempty)
    (fun p : ℕ × ℕ => dist (f p.1) (f p.2))
  simp only [Finset.mem_product, Finset.mem_range] at hp
  exact ⟨p.1, p.2, by omega, by omega, hpe.symm⟩

/-- `M_t ≤ B` as soon as all distances up to time `t` are `≤ B`. -/
theorem runningOsc_le_of {f : ℕ → E} {t : ℕ} {B : ℝ}
    (h : ∀ s s' : ℕ, s ≤ t → s' ≤ t → dist (f s) (f s') ≤ B) : runningOsc f t ≤ B :=
  Finset.sup'_le _ _ fun p hp => by
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact h p.1 p.2 (by omega) (by omega)

/-- `M_t ≥ 0`. -/
theorem runningOsc_nonneg (f : ℕ → E) (t : ℕ) : 0 ≤ runningOsc f t :=
  dist_nonneg.trans (dist_le_runningOsc f (Nat.zero_le t) (Nat.zero_le t))

/-- `M_t` is nondecreasing in `t`. -/
theorem runningOsc_mono (f : ℕ → E) {s t : ℕ} (h : s ≤ t) : runningOsc f s ≤ runningOsc f t :=
  runningOsc_le_of fun _ _ ha hb => dist_le_runningOsc f (ha.trans h) (hb.trans h)

/-- `M_0 = 0`. -/
@[simp] theorem runningOsc_zero (f : ℕ → E) : runningOsc f 0 = 0 :=
  le_antisymm (runningOsc_le_of fun a b ha hb => by
    obtain rfl : a = 0 := Nat.le_zero.1 ha
    obtain rfl : b = 0 := Nat.le_zero.1 hb
    simp) (runningOsc_nonneg f 0)

/-! ### The stopping rule and the times `τ^{(m)}_j` -/

/-- The stopping rule at level `m`, started at time `s`: it fires at `t ≥ s` when the path has moved
from `f s` by at least `2^{-m} M_t`, `M_t > 0` (Zorin-Kranich's notes, display (2.2), L36-L41). -/
def StopRule (f : ℕ → E) (m s t : ℕ) : Prop :=
  s ≤ t ∧ 0 < runningOsc f t ∧ (2⁻¹ : ℝ) ^ m * runningOsc f t ≤ dist (f t) (f s)

/-- The oscillation stopping times `τ^{(m)}_j ∈ ℕ ∪ {∞}` of Zorin-Kranich's notes, display (2.2):
`τ_0 = 0` and `τ_{j+1} = inf {t ≥ τ_j | StopRule f m τ_j t}`, `inf ∅ = ∞`. -/
def stopTime (f : ℕ → E) (m : ℕ) : ℕ → ℕ∞
  | 0 => 0
  | j + 1 => ⨅ (t : ℕ) (_ : ∃ s : ℕ, stopTime f m j = s ∧ StopRule f m s t), (t : ℕ∞)

@[simp] theorem stopTime_zero (f : ℕ → E) (m : ℕ) : stopTime f m 0 = 0 := rfl

/-- If the rule fires at `t`, then `τ_{j+1} ≤ t`. -/
theorem stopTime_succ_le {f : ℕ → E} {m j s t : ℕ} (hs : stopTime f m j = s)
    (h : StopRule f m s t) : stopTime f m (j + 1) ≤ t := by
  rw [stopTime]
  exact iInf₂_le t ⟨s, hs, h⟩

/-- Once `τ_j = ∞`, all later times are `∞`. -/
theorem stopTime_succ_eq_top_of_eq_top {f : ℕ → E} {m j : ℕ} (h : stopTime f m j = ⊤) :
    stopTime f m (j + 1) = ⊤ := by
  rw [stopTime]
  refine top_unique (le_iInf₂ fun t ht => ?_)
  obtain ⟨s, hs, -⟩ := ht
  exact absurd (h.symm.trans hs) (ENat.top_ne_natCast s)

/-- A finite `τ_{j+1} = b` is the first time at which the rule fires, started from the finite
`τ_j = s`; in particular the rule holds at `b` (the infimum is attained). -/
theorem exists_stopRule_of_stopTime_succ_eq {f : ℕ → E} {m j b : ℕ}
    (hb : stopTime f m (j + 1) = b) : ∃ s : ℕ, stopTime f m j = s ∧ StopRule f m s b := by
  classical
  have hex : ∃ t : ℕ, ∃ s : ℕ, stopTime f m j = s ∧ StopRule f m s t := by
    by_contra hne
    have h : stopTime f m (j + 1) = ⊤ := by
      rw [stopTime]
      refine top_unique (le_iInf₂ fun t ht => ?_)
      obtain ⟨s, hs, hr⟩ := ht
      exact absurd ⟨t, s, hs, hr⟩ hne
    rw [h] at hb
    exact absurd hb (ENat.top_ne_natCast b)
  obtain ⟨s, hs, hr⟩ := Nat.find_spec hex
  have h1 : stopTime f m (j + 1) = (Nat.find hex : ℕ) := by
    refine le_antisymm (stopTime_succ_le hs hr) ?_
    rw [stopTime]
    refine le_iInf₂ fun t ht => ?_
    exact_mod_cast Nat.find_min' hex ht
  have hbt : b = Nat.find hex := Nat.cast_injective (R := ℕ∞) (hb.symm.trans h1)
  rw [hbt]
  exact ⟨s, hs, hr⟩

/-- The rule holds at a finite `τ_{j+1}`. -/
theorem stopRule_of_stopTime_succ_eq {f : ℕ → E} {m j s b : ℕ} (hs : stopTime f m j = s)
    (hb : stopTime f m (j + 1) = b) : StopRule f m s b := by
  obtain ⟨s', hs', hr⟩ := exists_stopRule_of_stopTime_succ_eq hb
  obtain rfl : s' = s := Nat.cast_injective (R := ℕ∞) (hs'.symm.trans hs)
  exact hr

/-- Strictly between `τ_j` and `τ_{j+1}` the rule does not fire. -/
theorem not_stopRule_of_lt_stopTime_succ {f : ℕ → E} {m j s t : ℕ} (hs : stopTime f m j = s)
    (ht : (t : ℕ∞) < stopTime f m (j + 1)) : ¬ StopRule f m s t :=
  fun h => (stopTime_succ_le hs h).not_gt ht

/-- If the rule does not fire at `t ≥ s`, then `dist (f t) (f s) ≤ 2^{-m} M_t`
(the case `M_t = 0` included). -/
theorem dist_le_of_not_stopRule {f : ℕ → E} {m s t : ℕ} (hst : s ≤ t)
    (h : ¬ StopRule f m s t) : dist (f t) (f s) ≤ (2⁻¹ : ℝ) ^ m * runningOsc f t := by
  by_cases hM : 0 < runningOsc f t
  · exact (not_le.1 fun h' => h ⟨hst, hM, h'⟩).le
  · have h0 : runningOsc f t = 0 := le_antisymm (not_lt.1 hM) (runningOsc_nonneg f t)
    have := dist_le_runningOsc f (le_refl t) hst
    rw [h0] at this ⊢
    simpa using this

/-- `τ_j < τ_{j+1}` while `τ_j` is finite (strict increase of the partition). -/
theorem stopTime_lt_succ {f : ℕ → E} {m j s : ℕ} (hs : stopTime f m j = s) :
    stopTime f m j < stopTime f m (j + 1) := by
  by_contra hlt
  rw [not_lt, hs] at hlt
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top s) hlt)
  have hr := stopRule_of_stopTime_succ_eq hs hb.symm
  have hbs : b ≤ s := by exact_mod_cast hb ▸ hlt
  obtain rfl : b = s := le_antisymm hbs hr.1
  have h1 : 0 < (2⁻¹ : ℝ) ^ m * runningOsc f b := mul_pos (by positivity) hr.2.1
  have h2 := hr.2.2
  rw [dist_self] at h2
  linarith

/-- `τ_j ≤ τ_{j+1}`. -/
theorem stopTime_le_succ (f : ℕ → E) (m j : ℕ) : stopTime f m j ≤ stopTime f m (j + 1) := by
  by_cases h : stopTime f m j = ⊤
  · rw [stopTime_succ_eq_top_of_eq_top h]
    exact le_top
  · obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.1 h
    exact (stopTime_lt_succ hs.symm).le

/-- `τ_j ≥ j`: the times increase by at least one while they are finite. -/
theorem le_stopTime (f : ℕ → E) (m j : ℕ) : (j : ℕ∞) ≤ stopTime f m j := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases h : stopTime f m j = ⊤
    · rw [stopTime_succ_eq_top_of_eq_top h]
      exact le_top
    · obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.1 h
      have hlt := stopTime_lt_succ hs.symm
      have h1 : stopTime f m j + 1 ≤ stopTime f m (j + 1) := (ENat.add_one_le_iff h).2 hlt
      push_cast
      exact (add_le_add_left ih 1).trans h1

/-- For every time `t` there is a unique `j` with `τ_j ≤ t < τ_{j+1}`: the partition by the
times `τ_j` covers every `t ≥ 0`. -/
theorem exists_stopTime_le_lt (f : ℕ → E) (m t : ℕ) :
    ∃ j : ℕ, stopTime f m j ≤ t ∧ (t : ℕ∞) < stopTime f m (j + 1) := by
  classical
  have hex : ∃ j : ℕ, (t : ℕ∞) < stopTime f m j :=
    ⟨t + 1, lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self t) (le_stopTime f m (t + 1))⟩
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, stopTime_zero] at hspec
    exact absurd hspec (by simp)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  rw [hj] at hspec
  exact ⟨j, not_lt.1 (Nat.find_min hex (by omega)), hspec⟩

/-- Pathwise form of the stopping time property: `τ_{j+1} ≤ n` if and only if for some
`s ≤ t ≤ n` we have `τ_j = s` and the rule fires at `t`. -/
theorem stopTime_succ_le_iff {f : ℕ → E} {m j : ℕ} (n : ℕ) :
    stopTime f m (j + 1) ≤ n ↔
      ∃ s t : ℕ, t ≤ n ∧ stopTime f m j = s ∧ StopRule f m s t := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)
    obtain ⟨s, hs, hr⟩ := exists_stopRule_of_stopTime_succ_eq hb.symm
    exact ⟨s, b, by exact_mod_cast hb ▸ h, hs, hr⟩
  · rintro ⟨s, t, htn, hs, hr⟩
    exact (stopTime_succ_le hs hr).trans (by exact_mod_cast htn)

/-! ### Times on the horizon `[0, N]` -/

/-- `τ^{(m)}_j ∧ N` as a natural number: the times on the horizon `[0, N]`, with `τ = ∞`
replaced by `N` (the notes' convention `f_∞ := f_N`). It does not depend on the values of the path
after time `N`. -/
def sampleTime (f : ℕ → E) (N m j : ℕ) : ℕ := (min (stopTime f m j) (N : ℕ∞)).toNat

theorem coe_sampleTime (f : ℕ → E) (N m j : ℕ) :
    (sampleTime f N m j : ℕ∞) = min (stopTime f m j) (N : ℕ∞) :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top N) (min_le_right _ _))

/-- `τ_j ∧ N ≤ N`. -/
theorem sampleTime_le (f : ℕ → E) (N m j : ℕ) : sampleTime f N m j ≤ N := by
  have h : (sampleTime f N m j : ℕ∞) ≤ N := by
    rw [coe_sampleTime]
    exact min_le_right _ _
  exact_mod_cast h

/-- `τ_0 ∧ N = 0`. -/
@[simp] theorem sampleTime_zero (f : ℕ → E) (N m : ℕ) : sampleTime f N m 0 = 0 := by
  simp [sampleTime]

/-- A finite `τ_j = s ≤ N` is read as it is. -/
theorem sampleTime_eq_of_stopTime_eq {f : ℕ → E} {N m j s : ℕ} (hs : stopTime f m j = s)
    (hsN : s ≤ N) : sampleTime f N m j = s := by
  unfold sampleTime
  rw [hs, min_eq_left (by exact_mod_cast hsN)]
  exact ENat.toNat_natCast s

/-- For `s < N`: `τ_j ∧ N = s` iff `τ_j = s`. -/
theorem sampleTime_eq_iff {f : ℕ → E} {N m j s : ℕ} (hs : s < N) :
    sampleTime f N m j = s ↔ stopTime f m j = s := by
  refine ⟨fun h => ?_, fun h => sampleTime_eq_of_stopTime_eq h hs.le⟩
  have h1 : min (stopTime f m j) (N : ℕ∞) = s := by rw [← coe_sampleTime, h]
  rcases le_total (stopTime f m j) (N : ℕ∞) with hle | hle
  · rwa [min_eq_left hle] at h1
  · rw [min_eq_right hle] at h1
    exact absurd (by exact_mod_cast h1 : N = s) (by omega)

/-- For `n < N`: `τ_j ∧ N ≤ n` iff `τ_j ≤ n`. -/
theorem sampleTime_le_iff {f : ℕ → E} {N m j n : ℕ} (hn : n < N) :
    sampleTime f N m j ≤ n ↔ stopTime f m j ≤ n := by
  have h1 : sampleTime f N m j ≤ n ↔ (sampleTime f N m j : ℕ∞) ≤ n := by exact_mod_cast Iff.rfl
  rw [h1, coe_sampleTime, min_le_iff]
  have : ¬ (N : ℕ∞) ≤ n := by exact_mod_cast not_le.2 hn
  simp [this]

/-- For `j ≥ N` the time `τ_j ∧ N` equals `N` (at most `N` increments are nonzero). -/
theorem sampleTime_eq_of_le {f : ℕ → E} {N m j : ℕ} (hj : N ≤ j) : sampleTime f N m j = N := by
  unfold sampleTime
  have h : (N : ℕ∞) ≤ stopTime f m j :=
    (by exact_mod_cast hj : (N : ℕ∞) ≤ j).trans (le_stopTime f m j)
  rw [min_eq_right h]
  exact ENat.toNat_natCast N

/-- `τ_j ∧ N ≤ τ_{j+1} ∧ N`. -/
theorem sampleTime_le_succ (f : ℕ → E) (N m j : ℕ) :
    sampleTime f N m j ≤ sampleTime f N m (j + 1) := by
  have h : (sampleTime f N m j : ℕ∞) ≤ sampleTime f N m (j + 1) := by
    rw [coe_sampleTime, coe_sampleTime]
    exact min_le_min_right _ (stopTime_le_succ f m j)
  exact_mod_cast h

/-- Pathwise form of the stopping time property on the horizon `[0, N]`: for `n < N`,
`τ_{j+1} ∧ N ≤ n` iff for some `s ≤ t ≤ n` we have `τ_j ∧ N = s` and the rule fires at `t`. -/
theorem sampleTime_succ_le_iff {f : ℕ → E} {N m j n : ℕ} (hn : n < N) :
    sampleTime f N m (j + 1) ≤ n ↔
      ∃ s t : ℕ, t ≤ n ∧ sampleTime f N m j = s ∧ StopRule f m s t := by
  rw [sampleTime_le_iff hn, stopTime_succ_le_iff]
  refine exists_congr fun s => exists_congr fun t => and_congr_right fun htn => ?_
  refine and_congr_left fun hr => ?_
  exact (sampleTime_eq_iff (lt_of_le_of_lt (hr.1.trans htn) hn)).symm

end PrimeCarleson.Proof.Lepingle
