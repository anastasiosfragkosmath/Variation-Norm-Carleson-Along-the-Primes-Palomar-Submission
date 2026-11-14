module

public import PrimeCarleson.Proof.Fplus31.C2.CMainFacts
public import PrimeCarleson.Proof.Fplus31.Glue.Transport

/-!
# The Cramér-model comparison, the start of the iteration

Part of the start of the iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). From the
lower bound `e^{-p} ≤ ‖normLam N‖_{U³[N]}` of the norm: `exists_leng_start_interval`
(`G1/Start.lean`: the `U³` inverse theorem of the vendored library, with the transport of
`Glue/Transport.lean`) gives a `LengStart` of degree two on the interval
`{1, …, N} = apInt 1 0 1 N`, the state `LS N (normLam N) 2`, or a top-invariant niltest of degree
two, which descends (`exists_topInvariant_descent`) to the state `NS N (normLam N) 1`.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration Finset PrimeCarleson

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

/-- The interval `{1, …, N}` is the progression `apInt 1 0 1 N`. -/
theorem apPts_one (N : ℕ) : apPts 1 0 1 N = intervalPoints N := by
  unfold apPts apInt intervalPoints
  congr 1
  ext n
  simp [Int.modEq_one]

/-- The interval has `N` elements. -/
theorem card_apInt_one (N : ℕ) : (apInt 1 0 1 N).card = N := by
  rw [← card_apPts, apPts_one, card_intervalPoints]

/-- **The start of the iteration.** -/
theorem start_state :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {N : ℕ+} {p : ℝ}, 2 ≤ p → NormOK N →
      Real.exp (-p) ≤ gowersNormInterval 3 N (normLam N) →
      LS N (normLam N) 2 ((p + K) ^ K) ∨ NS N (normLam N) 1 ((p + K) ^ K) := by
  obtain ⟨C₀, hC₀, hstart⟩ := exists_leng_start_interval
  obtain ⟨C₁, hC₁, hdesc⟩ := exists_topInvariant_descent 1
  have hp1 : PB (fun p : ℝ => p + 1) := PB.id.add (PB.const 1 zero_le_one)
  have hp₀ : PB (fun p : ℝ => (p + 1 + C₀) ^ C₀) :=
    (PB.step C₀).comp hp1 (fun p hp => by linarith)
  have hp₂ : PB (fun p : ℝ => ((p + 1 + C₀) ^ C₀ + C₁) ^ C₁) :=
    (PB.step C₁).comp hp₀ (fun p hp => by
      have : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg C₀
      have h3 : (1 : ℝ) ≤ p + 1 + C₀ := by linarith
      calc (1 : ℝ) ≤ p + 1 + C₀ := h3
        _ ≤ (p + 1 + C₀) ^ C₀ := le_self_pow₀ h3 (by omega))
  obtain ⟨K, hK, hKn⟩ := hp₀.add hp₂
  refine ⟨K, hK, ?_⟩
  intro N p hp hNorm hG
  have hp1' : (1 : ℝ) ≤ p := by linarith
  have hneed := (hKn p hp1').2
  set p₀ : ℝ := (p + 1 + C₀) ^ C₀ with hp₀def
  set p₂ : ℝ := (p₀ + C₁) ^ C₁ with hp₂def
  have hp₀0 : 0 ≤ p₀ := by positivity
  have hp₂0 : 0 ≤ p₂ := by positivity
  set P : ℝ := (p + K) ^ K with hP
  have hNpos : 0 < (N : ℕ) := N.pos
  obtain ⟨hf1, hf2⟩ := interval_start_hypotheses (g := normLam N) hNorm hG
  have hAP : ∀ q : ℝ, 0 ≤ q → APInv (N : ℕ) q 1 0 1 (N : ℕ) := fun q hq =>
    ⟨le_rfl, by simpa using Real.one_le_exp hq, le_rfl, le_rfl⟩
  rcases hstart (N := (N : ℕ)) N.pos hp (fun x => normLam N (x ())) hf1 hf2 with
    hS | ⟨V, hVn, hVinv⟩
  · left
    obtain ⟨S⟩ := hS
    refine LS.mono (p := p₀) ⟨1, 0, 1, (N : ℕ), by rw [apPts_one]; exact S, hAP p₀ hp₀0, ?_⟩
      (by linarith)
    rw [card_apInt_one]
    have : Real.exp (-((p + 1 + C₀) ^ C₀)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [(Nat.cast_nonneg (α := ℝ) (N : ℕ))]
  · right
    obtain ⟨Nd, -, hc, hn, hev⟩ := hdesc V.model V.test hp₀0 V.complexity hVinv
    refine NS.mono (p := p₀ + p₂) ⟨1, 0, 1, (N : ℕ), Nd, hAP (p₀ + p₂) (by linarith),
      hc.mono (by linarith), ?_, ?_⟩ (by linarith)
    · rw [hn]; exact hVn
    · have hcorr := V.correlation
      have hcorr2 : Real.exp (-p₀) ≤ ‖𝔼 x ∈ apPts 1 0 1 (N : ℕ),
          (fun x : Unit → ℤ => normLam N (x ())) x * star (V.test.eval x)‖ := by
        rw [apPts_one]; exact hcorr
      rw [norm_expect_apPts, card_apInt_one, le_div_iff₀ (by exact_mod_cast hNpos)] at hcorr2
      have h1 : (N : ℝ) * Real.exp (-p₀) ≤
          ‖∑ n ∈ apInt 1 0 1 (N : ℕ), normLam N n * star (V.test.eval fun _ => n)‖ := by
        simpa [mul_comm] using hcorr2
      calc (N : ℝ) * Real.exp (-(p₀ + p₂)) ≤ N * Real.exp (-p₀) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
        _ ≤ _ := h1
        _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun n _ => by rw [hev]

end PrimeCarleson.Proof.Fplus31
