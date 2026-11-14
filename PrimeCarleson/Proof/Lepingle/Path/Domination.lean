module

public import PrimeCarleson.Proof.Lepingle.Path.ComparableJump
public import PrimeCarleson.Proof.Lepingle.Path.Variation

/-!
# Pathwise domination of the variation by the stopped increments

Source: Zorin-Kranich's notes `eq:ptw-domination` (02-Lepingle.tex, L94–L101) and
`eq:ptw-domination:only-square` (02-Lepingle.tex, L131–L137): displays (2.6) and (2.7) of
02-Lepingle.tex (L94-L137), for a path `f : ℕ → E` in a pseudo-metric space on the horizon
`[0, N]`.

Notation: `M_N = runningOsc f N`, `τ^{(m)}_j = stopTime f m j`, and
`sampleIncrement f N m j = dist (f (τ_j ∧ N)) (f (τ_{j+1} ∧ N))` (in `ℝ≥0∞`).

* `exists_level_of_jump`: the choice of the level `m(l) ≥ 2` and of the partition step `j(l)` for
  one increment of a chain (Zorin-Kranich's notes, L103-L116);
* `sum_rpow_chain_le`: for one chain, the termwise bound together with the injectivity of
  `l ↦ (m(l), j(l))` (each `τ^{(m)}_{j+1}` lies in one interval `(u_l, u_{l+1}]`);
* `seqVariationOn_rpow_le` (display (2.6)): for `0 < ρ < r`,
  `V^r(f; 0..N)^r ≤ 8^ρ ∑_{m ≥ 2} (2^{-(m-2)} M_N)^{r-ρ} ∑_j (increment_j^{(m)})^ρ`,
  with the sum over `m ≥ 2` written over `k = m - 2`;
* `seqVariationOn_rpow_le_tsum` (display (2.7)): `M_N` is cancelled
  against `V^r`, giving `V^r(f; 0..N)^ρ ≤ 8^ρ ∑_{m ≥ 2} 2^{-(m-2)(r-ρ)} ∑_j (…)^ρ`;
  `M_N ≤ V^r(f; 0..N) < ∞` are `ofReal_runningOsc_le_seqVariationOn` and `seqVariationOn_lt_top`.

The terms with `τ_{j+1} = ∞` (read at `N`) occur on the right but are never used on the left,
so the inequality holds with the printed convention `f_∞ := f_N`.
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Lepingle

variable {E : Type*} [PseudoMetricSpace E]

/-- The `j`-th increment of the path along the level-`m` partition on the horizon `[0, N]`:
`dist (f (τ_j ∧ N)) (f (τ_{j+1} ∧ N))`, valued in `ℝ≥0∞`. -/
def sampleIncrement (f : ℕ → E) (N m j : ℕ) : ℝ≥0∞ :=
  edist (f (sampleTime f N m j)) (f (sampleTime f N m (j + 1)))

/-- Beyond `j ≥ N` the increments vanish: `τ_j ∧ N = N`. -/
theorem sampleIncrement_eq_zero_of_le {f : ℕ → E} {N m j : ℕ} (hj : N ≤ j) :
    sampleIncrement f N m j = 0 := by
  simp [sampleIncrement, sampleTime_eq_of_le hj, sampleTime_eq_of_le (hj.trans (Nat.le_succ j))]

/-- The sum over `j` of the `ρ`-th powers of the increments is the finite sum over `j < N`. -/
theorem tsum_sampleIncrement_rpow {ρ : ℝ} (hρ : 0 < ρ) (f : ℕ → E) (N m : ℕ) :
    ∑' j : ℕ, sampleIncrement f N m j ^ ρ = ∑ j ∈ Finset.range N, sampleIncrement f N m j ^ ρ :=
  tsum_eq_sum fun j hj => by
    rw [sampleIncrement_eq_zero_of_le (by simpa using hj), ENNReal.zero_rpow_of_pos hρ]

/-- **The choice of level and step for one jump** (Zorin-Kranich's notes, L103-L116). If
`0 < dist (f t') (f t)` with `t' < t ≤ N`, there are a level `m = k + 2` and a step `j` of the
level-`m` partition, `τ_j = a`, `τ_{j+1} = b`, with `t' < b ≤ t` and
`dist (f t') (f t)^r ≤ 8^ρ dist (f a) (f b)^ρ (2^{-k} M_N)^{r-ρ}`, for `0 < ρ < r`. -/
theorem exists_level_of_jump {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (f : ℕ → E) {N t' t : ℕ}
    (htt : t' < t) (htN : t ≤ N) (hd : 0 < dist (f t') (f t)) :
    ∃ k j a b : ℕ, stopTime f (k + 2) j = a ∧ stopTime f (k + 2) (j + 1) = b ∧ t' < b ∧ b ≤ t ∧
      dist (f t') (f t) ^ r ≤
        8 ^ ρ * dist (f a) (f b) ^ ρ * ((2⁻¹ : ℝ) ^ k * runningOsc f N) ^ (r - ρ) := by
  classical
  set d := dist (f t') (f t) with hdd
  have hdM : d ≤ runningOsc f t := dist_le_runningOsc f htt.le le_rfl
  have hMpos : 0 < runningOsc f t := hd.trans_le hdM
  -- the level: `2^{-(k+1)} M_t < d ≤ 2^{-k} M_t`
  have hex : ∃ n : ℕ, (2⁻¹ : ℝ) ^ n * runningOsc f t < d := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hd hMpos) (by norm_num : (2⁻¹ : ℝ) < 1)
    exact ⟨n, by rwa [lt_div_iff₀ hMpos] at hn⟩
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have h := Nat.find_spec hex
    rw [h0, pow_zero, one_mul] at h
    exact absurd hdM (not_le.2 h)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have h1 : (2⁻¹ : ℝ) ^ (k + 1) * runningOsc f t < d := by
    have h := Nat.find_spec hex
    rwa [hk] at h
  have h2 : d ≤ (2⁻¹ : ℝ) ^ k * runningOsc f t :=
    not_lt.1 (Nat.find_min hex (by omega : k < Nat.find hex))
  obtain ⟨j, a, b, ha, hb, htb, hbt, hjump⟩ := exists_stopTime_comparable_jump (f := f)
    (m := k + 2) (by omega) htt
    (by calc 2 * ((2⁻¹ : ℝ) ^ (k + 2) * runningOsc f t)
            = (2⁻¹ : ℝ) ^ (k + 1) * runningOsc f t := by ring
          _ < d := h1)
    (by calc d ≤ (2⁻¹ : ℝ) ^ k * runningOsc f t := h2
          _ = 4 * ((2⁻¹ : ℝ) ^ (k + 2) * runningOsc f t) := by ring)
  refine ⟨k, j, a, b, ha, hb, htb, hbt, ?_⟩
  have hsplit : d ^ r = d ^ ρ * d ^ (r - ρ) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hA : d ^ ρ ≤ 8 ^ ρ * dist (f a) (f b) ^ ρ := by
    calc d ^ ρ ≤ (8 * dist (f a) (f b)) ^ ρ := Real.rpow_le_rpow hd.le hjump hρ.le
      _ = 8 ^ ρ * dist (f a) (f b) ^ ρ := Real.mul_rpow (by norm_num) dist_nonneg
  have hB : d ^ (r - ρ) ≤ ((2⁻¹ : ℝ) ^ k * runningOsc f N) ^ (r - ρ) := by
    refine Real.rpow_le_rpow hd.le (h2.trans ?_) (by linarith)
    exact mul_le_mul_of_nonneg_left (runningOsc_mono f htN) (by positivity)
  rw [hsplit]
  exact mul_le_mul hA hB (Real.rpow_nonneg hd.le _) (by positivity)

/-- `ofReal` of the termwise bound of `exists_level_of_jump`, as an `ℝ≥0∞` expression. -/
private theorem ofReal_term_eq {ρ q : ℝ} (hρ : 0 < ρ) (hq : 0 ≤ q) {X δ : ℝ} (hX : 0 ≤ X)
    (hδ : 0 ≤ δ) :
    ENNReal.ofReal (8 ^ ρ * δ ^ ρ * X ^ q) =
      8 ^ ρ * (ENNReal.ofReal X ^ q * ENNReal.ofReal δ ^ ρ) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg hX hq, ← ENNReal.ofReal_rpow_of_nonneg hδ hρ.le,
    ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) hρ.le, ENNReal.ofReal_ofNat]
  ring

/-- The counting step of Zorin-Kranich's notes, L117-L123: if every increment `e l` of a chain
`u₀ < ⋯ < u_J` with `P l` is dominated by a term `G p` whose time `τ p` lies in `(u_l, u_{l+1}]`,
then the sum of the increments is dominated by the sum of all the terms, because the intervals
`(u_l, u_{l+1}]` are pairwise disjoint (the map `l ↦ p` is injective). -/
theorem sum_le_tsum_of_choice {J : ℕ} {u : Fin (J + 1) → ℕ} (hu : StrictMono u)
    (P : Fin J → Prop) (e : Fin J → ℝ≥0∞) (he : ∀ l, ¬ P l → e l = 0)
    {ι : Type*} [Nonempty ι] (G : ι → ℝ≥0∞) (τ : ι → ℕ)
    (h : ∀ l, P l → ∃ p, u l.castSucc < τ p ∧ τ p ≤ u l.succ ∧ e l ≤ G p) :
    ∑ l, e l ≤ ∑' p, G p := by
  classical
  choose! φ hφ1 hφ2 hφ3 using h
  have hsucc : ∀ {l₁ l₂ : Fin J}, l₁ < l₂ → u l₁.succ ≤ u l₂.castSucc := fun h =>
    hu.monotone (Fin.succ_le_castSucc_iff.2 h)
  have hinj : Set.InjOn φ (↑(Finset.univ.filter P) : Set (Fin J)) := by
    intro l₁ h₁ l₂ h₂ h12
    have h₁' : P l₁ := (Finset.mem_filter.1 h₁).2
    have h₂' : P l₂ := (Finset.mem_filter.1 h₂).2
    have a1 := hφ1 l₁ h₁'
    have a2 := hφ2 l₁ h₁'
    have b1 := hφ1 l₂ h₂'
    have b2 := hφ2 l₂ h₂'
    rw [h12] at a1 a2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hsucc hlt
      omega
    · have := hsucc hlt
      omega
  calc ∑ l, e l = ∑ l ∈ Finset.univ.filter P, e l := by
        refine (Finset.sum_filter_of_ne fun l _ hl => ?_).symm
        by_contra hnot
        exact hl (he l hnot)
    _ ≤ ∑ l ∈ Finset.univ.filter P, G (φ l) :=
        Finset.sum_le_sum fun l hl => hφ3 l (Finset.mem_filter.1 hl).2
    _ = ∑ p ∈ (Finset.univ.filter P).image φ, G p := (Finset.sum_image hinj).symm
    _ ≤ ∑' p, G p := ENNReal.sum_le_tsum _

/-- The term `8^ρ (2^{-k} M_N)^{r-ρ} · increment^ρ` of the right-hand side of (2.6), at the level
`m = k + 2` and the step `j`. -/
def dominationTerm (f : ℕ → E) (N : ℕ) (r ρ : ℝ) (k j : ℕ) : ℝ≥0∞ :=
  8 ^ ρ * (ENNReal.ofReal ((2⁻¹ : ℝ) ^ k * runningOsc f N) ^ (r - ρ) *
    sampleIncrement f N (k + 2) j ^ ρ)

/-- One increment of a chain is dominated by one term of (2.6) whose time lies in
`(t', t]` (Zorin-Kranich's notes, L109-L116). -/
theorem exists_dominationTerm {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (f : ℕ → E) {N t' t : ℕ}
    (htt : t' < t) (htN : t ≤ N) (hd : 0 < dist (f t') (f t)) :
    ∃ p : ℕ × ℕ, t' < (stopTime f (p.1 + 2) (p.2 + 1)).toNat ∧
      (stopTime f (p.1 + 2) (p.2 + 1)).toNat ≤ t ∧
      edist (f t') (f t) ^ r ≤ dominationTerm f N r ρ p.1 p.2 := by
  have hr : 0 < r := hρ.trans hρr
  obtain ⟨k, j, a, b, ha, hb, htb, hbt, hle⟩ := exists_level_of_jump hρ hρr f (N := N) htt htN hd
  have hab : a ≤ b := (stopRule_of_stopTime_succ_eq ha hb).1
  have hbN : b ≤ N := hbt.trans htN
  have e1 : sampleTime f N (k + 2) j = a := sampleTime_eq_of_stopTime_eq ha (hab.trans hbN)
  have e2 : sampleTime f N (k + 2) (j + 1) = b := sampleTime_eq_of_stopTime_eq hb hbN
  have hXnn : 0 ≤ (2⁻¹ : ℝ) ^ k * runningOsc f N :=
    mul_nonneg (by positivity) (runningOsc_nonneg f N)
  refine ⟨(k, j), ?_, ?_, ?_⟩
  · simpa [hb] using htb
  · simpa [hb] using hbt
  · simp only [dominationTerm, sampleIncrement, e1, e2]
    rw [edist_dist (f a) (f b), edist_dist (f t') (f t),
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hr.le,
      ← ofReal_term_eq (q := r - ρ) hρ (by linarith) hXnn (dist_nonneg (x := f a) (y := f b))]
    exact ENNReal.ofReal_le_ofReal hle

/-- **Domination along one chain** (Zorin-Kranich's notes, L102-L124): for a chain
`u₀ < ⋯ < u_J ≤ N`, the sum of the `r`-th powers of its increments is at most
`8^ρ ∑_{m ≥ 2} (2^{-(m-2)} M_N)^{r-ρ} ∑_j (increment of the level-m partition)^ρ`. -/
theorem sum_rpow_chain_le {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (f : ℕ → E) (N : ℕ) {J : ℕ}
    {u : Fin (J + 1) → ℕ} (hu : StrictMono u) (hN : ∀ i, u i ≤ N) :
    ∑ i : Fin J, edist (f (u i.castSucc)) (f (u i.succ)) ^ r ≤
      8 ^ ρ * ∑' k : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ k * runningOsc f N) ^ (r - ρ) *
        ∑' j : ℕ, sampleIncrement f N (k + 2) j ^ ρ := by
  have hr : 0 < r := hρ.trans hρr
  have h := sum_le_tsum_of_choice hu
    (fun l => 0 < dist (f (u l.castSucc)) (f (u l.succ)))
    (fun l => edist (f (u l.castSucc)) (f (u l.succ)) ^ r)
    (fun l hl => by
      have h0 : dist (f (u l.castSucc)) (f (u l.succ)) = 0 :=
        le_antisymm (not_lt.1 hl) dist_nonneg
      rw [edist_dist, h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hr])
    (fun p : ℕ × ℕ => dominationTerm f N r ρ p.1 p.2)
    (fun p => (stopTime f (p.1 + 2) (p.2 + 1)).toNat)
    (fun l hl => exists_dominationTerm hρ hρr f (hu (Fin.castSucc_lt_succ (i := l))) (hN _) hl)
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.tsum_prod (f := fun k j => dominationTerm f N r ρ k j)]
  simp only [dominationTerm, ENNReal.tsum_mul_left]

/-- **Pathwise domination (2.6)** (Zorin-Kranich's notes, L94-L124): for `0 < ρ < r`,
`V^r(f; 0..N)^r ≤ 8^ρ ∑_{m ≥ 2} (2^{-(m-2)} M_N)^{r-ρ} ∑_j (increment_j^{(m)})^ρ`
with `increment_j^{(m)} = dist (f τ^{(m)}_j) (f τ^{(m)}_{j+1})` (`sampleIncrement`), the sum over
`m ≥ 2` written over `k = m - 2`, times read on the horizon `[0, N]`. -/
theorem seqVariationOn_rpow_le {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (f : ℕ → E) (N : ℕ) :
    seqVariationOn r f N ^ r ≤
      8 ^ ρ * ∑' k : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ k * runningOsc f N) ^ (r - ρ) *
        ∑' j : ℕ, sampleIncrement f N (k + 2) j ^ ρ := by
  have hr : 0 < r := hρ.trans hρr
  set B : ℝ≥0∞ := 8 ^ ρ * ∑' k : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ k * runningOsc f N) ^ (r - ρ) *
    ∑' j : ℕ, sampleIncrement f N (k + 2) j ^ ρ with hB
  have h : seqVariationOn r f N ≤ B ^ (1 / r) :=
    seqVariationOn_le fun J u hu hN =>
      ENNReal.rpow_le_rpow (sum_rpow_chain_le hρ hρr f N hu hN) (by positivity)
  calc seqVariationOn r f N ^ r ≤ (B ^ (1 / r)) ^ r := ENNReal.rpow_le_rpow h hr.le
    _ = B := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]

/-- **Cancelling the oscillation** (display (2.7), Zorin-Kranich's notes, L126-L137): for
`0 < ρ < r`,
`V^r(f; 0..N)^ρ ≤ 8^ρ ∑_{m ≥ 2} 2^{-(m-2)(r-ρ)} ∑_j dist (f τ^{(m)}_j) (f τ^{(m)}_{j+1})^ρ`
(`k = m - 2`; the weight is written `(2^{-k})^{r-ρ}`). The proof uses
`M_N ≤ V^r(f; 0..N) < ∞`, the printed `M_∞ ≤ V^r_t(f_t) < ∞`. -/
theorem seqVariationOn_rpow_le_tsum {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (f : ℕ → E) (N : ℕ) :
    seqVariationOn r f N ^ ρ ≤
      8 ^ ρ * ∑' k : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) ^ (r - ρ) *
        ∑' j : ℕ, sampleIncrement f N (k + 2) j ^ ρ := by
  have hr : 0 < r := hρ.trans hρr
  have hrρ : 0 ≤ r - ρ := sub_nonneg.2 hρr.le
  set V := seqVariationOn r f N with hV
  have hdom := seqVariationOn_rpow_le hρ hρr f N
  have hVtop : V < ⊤ := seqVariationOn_lt_top hr f N
  have hMV : ENNReal.ofReal (runningOsc f N) ≤ V := ofReal_runningOsc_le_seqVariationOn hr f N
  by_cases hV0 : V = 0
  · rw [hV0, ENNReal.zero_rpow_of_pos hρ]
    exact zero_le
  set A : ℕ → ℝ≥0∞ := fun k => ∑' j : ℕ, sampleIncrement f N (k + 2) j ^ ρ with hA
  set T : ℝ≥0∞ := ∑' k : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) ^ (r - ρ) * A k with hT
  have hterm : ∀ k : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ k * runningOsc f N) ^ (r - ρ) * A k ≤
      V ^ (r - ρ) * (ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) ^ (r - ρ) * A k) := by
    intro k
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hrρ]
    calc ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) ^ (r - ρ) * ENNReal.ofReal (runningOsc f N) ^ (r - ρ) * A k
        ≤ ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) ^ (r - ρ) * V ^ (r - ρ) * A k := by
          gcongr
      _ = V ^ (r - ρ) * (ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) ^ (r - ρ) * A k) := by ring
  have h1 : V ^ r = V ^ ρ * V ^ (r - ρ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hρ.le hrρ]
    congr 1
    ring
  have h2 : V ^ ρ * V ^ (r - ρ) ≤ (8 ^ ρ * T) * V ^ (r - ρ) := by
    rw [← h1]
    calc V ^ r ≤ 8 ^ ρ * ∑' k : ℕ,
            ENNReal.ofReal ((2⁻¹ : ℝ) ^ k * runningOsc f N) ^ (r - ρ) * A k := hdom
      _ ≤ 8 ^ ρ * ∑' k : ℕ, V ^ (r - ρ) * (ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) ^ (r - ρ) * A k) :=
          mul_le_mul_right (ENNReal.tsum_le_tsum hterm) _
      _ = (8 ^ ρ * T) * V ^ (r - ρ) := by
          rw [ENNReal.tsum_mul_left, hT]
          ring
  have hc0 : V ^ (r - ρ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hV0) hVtop.ne).ne'
  have hctop : V ^ (r - ρ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hrρ hVtop.ne
  exact (ENNReal.mul_le_mul_iff_left hc0 hctop).1 h2

end PrimeCarleson.Proof.Lepingle
