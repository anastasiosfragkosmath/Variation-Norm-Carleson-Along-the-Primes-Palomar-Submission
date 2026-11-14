module

public import PrimeCarleson.Proof.Lepingle.Path.StoppingTimes
public import PrimeCarleson.Proof.Common.Variation

/-!
# The `r`-variation of a path up to a time `N`

Source: [O+] `definitionofvariation`, L601–L628 (as used by Zorin-Kranich's notes, display (2.1),
L3-L13).

For a path `f : ℕ → E` in a pseudo-metric space,
`seqVariationOn r f N = V^r(f; 0..N)` is the supremum, over strictly increasing chains
`u₀ < ⋯ < u_J ≤ N` of natural numbers, of `(∑ᵢ dist (f u_{i}) (f u_{i+1})^r)^{1/r}`, valued in
`ℝ≥0∞` and written with `edist` exactly as `PrimeCarleson.rVariationOn`.

Zorin-Kranich's notes (02-Lepingle.tex L32) reduce to martingales that become constant after some
time `N`. The argument here never needs `f` to be constant: the bounds are proved for
`V^r(f; 0..N)` with the times truncated at `N` (`sampleTime`).

Also: `ofReal_runningOsc_le_seqVariationOn` (`M_N ≤ V^r(f; 0..N)`, the one-step chain) and
`seqVariationOn_lt_top` (`V^r(f; 0..N) < ∞` for `r > 0`), the two facts used to cancel a power of
the variation in display (2.7).
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

open PrimeCarleson PrimeCarleson.Proof.MswTransference PrimeCarleson.Proof.Common

variable {E : Type*} [PseudoMetricSpace E]

/-- The `r`-variation of a path `f : ℕ → E` over the times `0, …, N`:
`V^r(f; 0..N) = sup_{u₀ < ⋯ < u_J ≤ N} (∑ᵢ dist (f u_i) (f u_{i+1})^r)^{1/r}` (Zorin-Kranich's
notes, display (2.1) on the interval `[0, N]`; the chains are strictly increasing sequences of
natural numbers). -/
def seqVariationOn (r : ℝ) (f : ℕ → E) (N : ℕ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (u : Fin (J + 1) → ℕ) (_ : StrictMono u) (_ : ∀ i, u i ≤ N),
    (∑ i : Fin J, edist (f (u i.castSucc)) (f (u i.succ)) ^ r) ^ (1 / r)

/-- The variation is bounded by `B` once every chain gives a value at most `B`. -/
theorem seqVariationOn_le {r : ℝ} {f : ℕ → E} {N : ℕ} {B : ℝ≥0∞}
    (h : ∀ (J : ℕ) (u : Fin (J + 1) → ℕ), StrictMono u → (∀ i, u i ≤ N) →
      (∑ i : Fin J, edist (f (u i.castSucc)) (f (u i.succ)) ^ r) ^ (1 / r) ≤ B) :
    seqVariationOn r f N ≤ B :=
  iSup_le fun J => iSup_le fun u => iSup_le fun hu => iSup_le fun hN => h J u hu hN

/-- Every chain gives a value at most the variation. -/
theorem le_seqVariationOn {r : ℝ} {f : ℕ → E} {N J : ℕ} {u : Fin (J + 1) → ℕ}
    (hu : StrictMono u) (hN : ∀ i, u i ≤ N) :
    (∑ i : Fin J, edist (f (u i.castSucc)) (f (u i.succ)) ^ r) ^ (1 / r) ≤ seqVariationOn r f N :=
  le_iSup₂_of_le J u <| le_iSup₂_of_le hu hN le_rfl

/-- A strictly increasing chain `u : Fin (J + 1) → ℕ` with values `≤ N` has length `J ≤ N`. -/
theorem chain_length_le {J N : ℕ} {u : Fin (J + 1) → ℕ} (hu : StrictMono u)
    (hN : ∀ i, u i ≤ N) : J ≤ N := by
  have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (J + 1))))
    (t := Finset.range (N + 1)) u
    (fun i _ => Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le (hN i))))
    hu.injective.injOn
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_range] at this
  omega

/-- One increment `a < b ≤ N` is a chain: `dist (f a) (f b) ≤ V^r(f; 0..N)` for `r > 0`. -/
theorem edist_le_seqVariationOn {r : ℝ} (hr : 0 < r) (f : ℕ → E) {N a b : ℕ} (hab : a < b)
    (hb : b ≤ N) : edist (f a) (f b) ≤ seqVariationOn r f N := by
  have hu : StrictMono (![a, b] : Fin (1 + 1) → ℕ) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simpa using hab
  have h := le_seqVariationOn (r := r) (f := f) (N := N) hu (fun i => by
    fin_cases i
    · simpa using (hab.le.trans hb)
    · simpa using hb)
  have h2 : (∑ i : Fin 1, edist (f ((![a, b] : Fin (1 + 1) → ℕ) i.castSucc))
      (f ((![a, b] : Fin (1 + 1) → ℕ) i.succ)) ^ r) = edist (f a) (f b) ^ r := by simp
  have e : (edist (f a) (f b) ^ r) ^ (1 / r) = edist (f a) (f b) := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
  rwa [h2, e] at h

/-- `M_N ≤ V^r(f; 0..N)` for `r > 0`: the running oscillation is a one-step chain. -/
theorem ofReal_runningOsc_le_seqVariationOn {r : ℝ} (hr : 0 < r) (f : ℕ → E) (N : ℕ) :
    ENNReal.ofReal (runningOsc f N) ≤ seqVariationOn r f N := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_dist_eq_runningOsc f N
  rw [← hxy, ← edist_dist]
  rcases lt_trichotomy x y with h | rfl | h
  · exact edist_le_seqVariationOn hr f h hy
  · simp
  · rw [edist_comm]
    exact edist_le_seqVariationOn hr f h hx

/-- `V^r(f; 0..N) < ∞` for `r > 0`: a chain in `[0, N]` has at most `N` steps, each of size
at most `M_N`. -/
theorem seqVariationOn_lt_top {r : ℝ} (hr : 0 < r) (f : ℕ → E) (N : ℕ) :
    seqVariationOn r f N < ⊤ := by
  set B : ℝ≥0∞ := (N : ℝ≥0∞) * ENNReal.ofReal (runningOsc f N) ^ r with hB
  have hBtop : B < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top N)
      (ENNReal.rpow_lt_top_of_nonneg hr.le ENNReal.ofReal_ne_top)
  refine lt_of_le_of_lt (seqVariationOn_le (B := B ^ (1 / r)) fun J u hu hN => ?_)
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hBtop.ne)
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  calc ∑ i : Fin J, edist (f (u i.castSucc)) (f (u i.succ)) ^ r
      ≤ ∑ _i : Fin J, ENNReal.ofReal (runningOsc f N) ^ r := by
        refine Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow ?_ hr.le
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (dist_le_runningOsc f (hN _) (hN _))
    _ = (J : ℝ≥0∞) * ENNReal.ofReal (runningOsc f N) ^ r := by simp
    _ ≤ B := by
        rw [hB]
        gcongr
        exact_mod_cast chain_length_le hu hN

end PrimeCarleson.Proof.Lepingle
