module

public import PrimeCarleson.Proof.Lepingle.Prob.GarsiaNeveu
public import Mathlib.Probability.Process.Filtration

/-!
# Garsia-Neveu for predictable increasing processes

Source: Zorin-Kranich's notes `cor:Garsia-Neveu` (01-BDG.tex, L413–L423): Corollary 1.12
(L413-L439): if `(A_t)` is an increasing predictable process
with `A_0 = 0` and `ξ ≥ 0` satisfies `E_t(A_∞ - A_t) ≤ E_t ξ` for every `t`, then
`‖A_∞‖_p ≤ p ‖ξ‖_p` for `p ≥ 1`.

The hypothesis `E_t(A_∞ - A_t) ≤ E_t ξ` is stated in its integrated form
`∫_B (A_∞ - A_t) ≤ ∫_B ξ` for all `B ∈ ℱ t` (this is item (7) of the properties of conditional
expectation; for integrable data the two forms are
equivalent), which makes sense for `ℝ≥0∞`-valued data without
integrability assumptions.  Predictability is `Measurable[ℱ t] (A (t + 1))`.

The proof does not use stopping times: the events `{A_t ≤ λ < A_{t+1}}` (`ℱ t`-measurable by
predictability) are the disjoint level sets `{τ = t}` of `τ = inf{t : A_{t+1} > λ}` of the paper.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Garsia-Neveu for predictable increasing processes** (Zorin-Kranich's notes, Corollary 1.12;
constant exactly `p`).  `A` is increasing in `t`, `A 0 = 0`, `A (t+1)` is
`ℱ t`-measurable (predictable), `ξ` is measurable, and for every `t` and `B ∈ ℱ t`,
`∫_B (A_∞ - A_t) ≤ ∫_B ξ` where `A_∞ = sup_t A_t`. -/
theorem garsia_neveu_cor [IsFiniteMeasure μ] (ℱ : MeasureTheory.Filtration ℕ m0)
    {A : ℕ → Ω → ℝ≥0∞} {ξ : Ω → ℝ≥0∞} (hA0 : A 0 = 0)
    (hmono : ∀ ω, Monotone fun t => A t ω) (hpred : ∀ t, Measurable[ℱ t] (A (t + 1)))
    (hξ : Measurable ξ)
    (h : ∀ t : ℕ, ∀ B : Set Ω, MeasurableSet[ℱ t] B →
      ∫⁻ ω in B, ((⨆ s, A s ω) - A t ω) ∂μ ≤ ∫⁻ ω in B, ξ ω ∂μ)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, (⨆ s, A s ω) ^ p ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal p * (∫⁻ ω, ξ ω ^ p ∂μ) ^ (1 / p) := by
  have hAt : ∀ t, Measurable[ℱ t] (A t) := by
    intro t
    cases t with
    | zero => rw [hA0]; exact measurable_const
    | succ s => exact (hpred s).mono (ℱ.mono s.le_succ) le_rfl
  have hAm : ∀ t, Measurable (A t) := fun t => (hAt t).mono (ℱ.le t) le_rfl
  have hW : Measurable fun ω => ⨆ s, A s ω := Measurable.iSup hAm
  refine garsia_neveu hW hξ ?_ hp
  intro l hl
  set L : ℝ≥0∞ := ENNReal.ofReal l with hL
  -- the level sets `{A_t ≤ L < A_{t+1}}`
  let Bt : ℕ → Set Ω := fun t => {ω | A t ω ≤ L} ∩ {ω | L < A (t + 1) ω}
  have hBt : ∀ t, MeasurableSet[ℱ t] (Bt t) := fun t =>
    (measurableSet_le (hAt t) measurable_const).inter
      (measurableSet_lt measurable_const (hpred t))
  have hBtm : ∀ t, MeasurableSet (Bt t) := fun t => ℱ.le t _ (hBt t)
  have hdisj : Pairwise (Function.onFun Disjoint Bt) := by
    intro s t hst
    wlog hlt : s < t generalizing s t
    · exact (this hst.symm (lt_of_le_of_ne (not_lt.1 hlt) hst.symm)).symm
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h3, h4⟩
    have := hmono ω (Nat.succ_le_of_lt hlt)
    exact absurd (lt_of_lt_of_le h2 (this.trans h3)) (lt_irrefl _)
  have hunion : (⋃ t, Bt t) = {ω | L < ⨆ s, A s ω} := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq, mem_inter_iff, Bt]
    constructor
    · rintro ⟨t, _, h2⟩
      exact lt_of_lt_of_le h2 (le_iSup (fun s => A s ω) (t + 1))
    · intro hω
      have hex : ∃ t, L < A (t + 1) ω := by
        obtain ⟨s, hs⟩ := lt_iSup_iff.1 hω
        cases s with
        | zero => rw [hA0] at hs; exact absurd hs (by simp)
        | succ u => exact ⟨u, hs⟩
      classical
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
      cases ht : Nat.find hex with
      | zero => rw [hA0]; exact zero_le
      | succ u =>
        have := Nat.find_min hex (show u < Nat.find hex by omega)
        exact not_lt.1 this
  have hsetS : {ω | ENNReal.ofReal l < ⨆ s, A s ω} = ⋃ t, Bt t := by rw [hunion]
  rw [hsetS, lintegral_iUnion hBtm hdisj, lintegral_iUnion hBtm hdisj]
  refine ENNReal.tsum_le_tsum fun t => ?_
  calc ∫⁻ ω in Bt t, ((⨆ s, A s ω) - L) ∂μ ≤ ∫⁻ ω in Bt t, ((⨆ s, A s ω) - A t ω) ∂μ :=
        setLIntegral_mono' (hBtm t) fun ω hω => tsub_le_tsub_left hω.1 _
    _ ≤ ∫⁻ ω in Bt t, ξ ω ∂μ := h t (Bt t) (hBt t)

end PrimeCarleson.Proof.Lepingle
