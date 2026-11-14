module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Time-ordered nets for the entropy lemma

Part of a self-contained chaining proof of main paper `l:entest` (L1824–L1860), which the paper
obtains from [ZK15, Lemma 2.6]: nets built in time order, their parent map and the count of the
stopping times.

The family is `c : ℕ → H` in a normed group, enumerated by the indices `0, …, N-1` (the paper's
`1, …, N`). For a threshold `θ ≥ 0` the ancestor map `π_θ = net c θ` is defined by recursion on `j`:

  `π(0) = 0`, `π(j+1) = j+1` if `θ < ‖c(j+1) - c(π(j))‖`, else `π(j+1) = π(j)`.

The stopping times are `stops c θ N = {j < N : π(j) = j}`. The hypothesis (V) of Theorem A is the
chain-wise bound `ChainBound c N s λ`.

* `monotone_net`, `net_le_self`, `net_net`, `net_succ_eq`: `π` is nondecreasing, `π(j) ≤ j`,
  `π(π(j)) = π(j)` and `π(j+1) ∈ {π(j), j+1}`;
* `norm_sub_net_le`: the net property `‖c_j - c_{π(j)}‖ ≤ θ`;
* `lt_norm_sub_of_consecutive`: separation of consecutive stops;
* `net_eq_zero_of_chainBound`: level 0, `π_λ ≡ 0`;
* `card_stops_lt`, `card_levelStops_lt`: the count `M_v < 2^{v s}` (`|Λ_v| < 2^{vs} + 1`) and
  `|U_v| < (3/2) 2^{vs}`, using (V) and `s > 2`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

variable {H : Type*} [NormedAddCommGroup H]

/-- The stopping-time ancestor map of threshold `θ`: `π(0) = 0` and `π(j+1) = j+1` if
`c_{j+1}` is farther than `θ` from the last stop `c_{π(j)}`, otherwise `π(j+1) = π(j)`. -/
def net (c : ℕ → H) (θ : ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if θ < ‖c (j + 1) - c (net c θ j)‖ then j + 1 else net c θ j

/-- The stopping times of threshold `θ` among the first `N` indices: `Λ = {j < N : π(j) = j}`. -/
def stops (c : ℕ → H) (θ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun j => net c θ j = j

/-- Hypothesis (V) of Theorem A for the first `N` indices: every chain of indices
`j₀ < ⋯ < j_K < N` has `∑ ‖c_{j_k} - c_{j_{k+1}}‖^s ≤ λ^s`. -/
def ChainBound (c : ℕ → H) (N : ℕ) (s lam : ℝ) : Prop :=
  ∀ (K : ℕ) (j : Fin (K + 1) → ℕ), StrictMono j → (∀ k, j k < N) →
    ∑ k : Fin K, ‖c (j k.castSucc) - c (j k.succ)‖ ^ s ≤ lam ^ s

section Net

variable (c : ℕ → H) (θ : ℝ)

/-- `π(0) = 0`. -/
@[simp] theorem net_zero : net c θ 0 = 0 := rfl

/-- The defining recursion of `π` at `j + 1`. -/
theorem net_succ (j : ℕ) :
    net c θ (j + 1) = if θ < ‖c (j + 1) - c (net c θ j)‖ then j + 1 else net c θ j := rfl

/-- `π(j) ≤ j`. -/
theorem net_le_self (j : ℕ) : net c θ j ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [net_succ]
    split_ifs
    · exact le_rfl
    · exact ih.trans (Nat.le_succ j)

/-- `π(j+1) ∈ {π(j), j+1}`. -/
theorem net_succ_eq (j : ℕ) : net c θ (j + 1) = j + 1 ∨ net c θ (j + 1) = net c θ j := by
  rw [net_succ]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `π(π(j)) = π(j)`: the value `π(j)` is a stopping time. -/
theorem net_net (j : ℕ) : net c θ (net c θ j) = net c θ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases net_succ_eq c θ j with h | h
    · rw [h, h]
    · rw [h, ih]

/-- `π` is nondecreasing (the ancestor map is monotone). -/
theorem monotone_net : Monotone (net c θ) := by
  refine monotone_nat_of_le_succ fun j => ?_
  rcases net_succ_eq c θ j with h | h
  · rw [h]; exact (net_le_self c θ j).trans (Nat.le_succ j)
  · rw [h]

/-- The net property: `‖c_j - c_{π(j)}‖ ≤ θ`. -/
theorem norm_sub_net_le (hθ : 0 ≤ θ) (j : ℕ) : ‖c j - c (net c θ j)‖ ≤ θ := by
  induction j with
  | zero => simpa using hθ
  | succ j ih =>
    rw [net_succ]
    split_ifs with h
    · simpa using hθ
    · exact not_lt.1 h

/-- Separation of consecutive stops: if `j+1` is a stopping time, then
`θ < ‖c_{j+1} - c_{π(j)}‖`, where `π(j)` is the previous stopping time. -/
theorem lt_norm_sub_net_of_net_succ_eq {j : ℕ} (h : net c θ (j + 1) = j + 1) :
    θ < ‖c (j + 1) - c (net c θ j)‖ := by
  by_contra hlt
  have : net c θ (j + 1) = net c θ j := by rw [net_succ]; simp [hlt]
  have h2 := net_le_self c θ j
  omega

/-- Level 0: if all `c_j` are within `θ` of `c_0` (`j < N`), the net is trivial: `π ≡ 0`
on `[0, N)`. -/
theorem net_eq_zero_of_norm_le {N : ℕ} (h : ∀ j < N, ‖c j - c 0‖ ≤ θ) :
    ∀ j < N, net c θ j = 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    rw [net_succ, h1]
    have : ¬ θ < ‖c (j + 1) - c 0‖ := not_lt.2 (h _ hj)
    simp [this]

/-- The net is idempotent, monotone and below the identity; for such maps `p`, if
`p j ≤ m ≤ j` then `p m = p j`. -/
theorem net_eq_of_between {j m : ℕ} (h1 : net c θ j ≤ m) (h2 : m ≤ j) :
    net c θ m = net c θ j := by
  refine le_antisymm ((monotone_net c θ h2)) ?_
  calc net c θ j = net c θ (net c θ j) := (net_net c θ j).symm
    _ ≤ net c θ m := monotone_net c θ h1

/-- Maximal characterization: `π(j) = max {τ ∈ Λ : τ ≤ j}`; for a stopping time `τ ≤ j`
one has `τ ≤ π(j)`. -/
theorem le_net_of_net_eq_self {j τ : ℕ} (hτ : net c θ τ = τ) (hle : τ ≤ j) : τ ≤ net c θ j := by
  calc τ = net c θ τ := hτ.symm
    _ ≤ net c θ j := monotone_net c θ hle

/-- **Separation of consecutive stops**: if `a < b` are stopping times with no stopping
time strictly between them, then `π(b - 1) = a` and `θ < ‖c_b - c_a‖`. -/
theorem lt_norm_sub_of_consecutive {a b : ℕ} (hab : a < b) (ha : net c θ a = a)
    (hb : net c θ b = b) (hbetween : ∀ τ, a < τ → τ < b → net c θ τ ≠ τ) :
    net c θ (b - 1) = a ∧ θ < ‖c b - c a‖ := by
  obtain ⟨j', rfl⟩ : ∃ j', b = j' + 1 := ⟨b - 1, by omega⟩
  have h1 : a ≤ net c θ j' := le_net_of_net_eq_self c θ ha (by omega)
  have hpa : net c θ j' = a := by
    by_contra hne
    exact hbetween (net c θ j') (lt_of_le_of_ne h1 (Ne.symm hne))
      (lt_of_le_of_lt (net_le_self c θ j') (by omega)) (net_net c θ j')
  have hsep := lt_norm_sub_net_of_net_succ_eq c θ hb
  rw [hpa] at hsep
  exact ⟨by simpa using hpa, hsep⟩

end Net

/-- A stopping time below `N` is mapped to itself. -/
theorem mem_stops_iff {c : ℕ → H} {θ : ℝ} {N j : ℕ} :
    j ∈ stops c θ N ↔ j < N ∧ net c θ j = j := by
  simp [stops]

/-- `π(j)` is a stopping time. -/
theorem net_mem_stops {c : ℕ → H} {θ : ℝ} {N j : ℕ} (hj : j < N) :
    net c θ j ∈ stops c θ N :=
  mem_stops_iff.2 ⟨lt_of_le_of_lt (net_le_self c θ j) hj, net_net c θ j⟩

/-- The first index is a stopping time. -/
theorem zero_mem_stops {c : ℕ → H} {θ : ℝ} {N : ℕ} (hN : 0 < N) : 0 ∈ stops c θ N :=
  mem_stops_iff.2 ⟨hN, rfl⟩

section ChainBound

variable {c : ℕ → H} {N : ℕ} {s lam : ℝ}

/-- Two-point chains: under (V), `‖c_i - c_j‖ ≤ λ` for all `i, j < N`. -/
theorem ChainBound.norm_sub_le (hV : ChainBound c N s lam) (hs : 0 < s) (hlam : 0 ≤ lam)
    {i j : ℕ} (hi : i < N) (hj : j < N) : ‖c i - c j‖ ≤ lam := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h := hV 1 ![i, j] (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all) (by
      intro k; fin_cases k <;> simp [hi, hj])
    simp only [Fin.sum_univ_one] at h
    simpa using (Real.rpow_le_rpow_iff (norm_nonneg _) hlam hs).1 h
  · simpa using hlam
  · have h := hV 1 ![j, i] (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all) (by
      intro k; fin_cases k <;> simp [hi, hj])
    simp only [Fin.sum_univ_one] at h
    rw [norm_sub_rev]
    simpa using (Real.rpow_le_rpow_iff (norm_nonneg _) hlam hs).1 h

/-- Level 0: under (V) the net of threshold `λ` is trivial on `[0, N)`. -/
theorem net_eq_zero_of_chainBound (hV : ChainBound c N s lam) (hs : 0 < s) (hlam : 0 ≤ lam)
    {j : ℕ} (hj : j < N) : net c lam j = 0 :=
  net_eq_zero_of_norm_le c lam (fun _ h => hV.norm_sub_le hs hlam h (by omega)) j hj

/-- **Counting**: under (V) with `λ > 0`, `s > 0`, the stopping times of threshold
`λ 2^{-v}` satisfy `|Λ_v| < 2^{v s} + 1`, i.e. `M_v = |Λ_v| - 1 < 2^{v s}`.

Part of the chaining proof of main paper `l:entest` (L1824–L1860). -/
theorem card_stops_lt (hV : ChainBound c N s lam) (hs : 0 < s) (hlam : 0 < lam) (hN : 0 < N)
    (v : ℕ) : ((stops c (lam / 2 ^ v) N).card : ℝ) < (2 : ℝ) ^ ((v : ℝ) * s) + 1 := by
  set θ : ℝ := lam / 2 ^ v with hθdef
  have hθ : 0 < θ := by positivity
  set L := stops c θ N with hL
  obtain ⟨M, hM⟩ : ∃ M, L.card = M + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.2 ⟨0, zero_mem_stops hN⟩)
  set e := L.orderEmbOfFin hM with he
  have hLmem : ∀ k, e k ∈ L := fun k => Finset.orderEmbOfFin_mem _ _ _
  have hlt : ∀ k, e k < N := fun k => (mem_stops_iff.1 (hLmem k)).1
  have hfix : ∀ k, net c θ (e k) = e k := fun k => (mem_stops_iff.1 (hLmem k)).2
  have hsep : ∀ k : Fin M, θ < ‖c (e k.castSucc) - c (e k.succ)‖ := by
    intro k
    have hab : e k.castSucc < e k.succ := e.strictMono Fin.castSucc_lt_succ
    have hbetween : ∀ τ, e k.castSucc < τ → τ < e k.succ → net c θ τ ≠ τ := by
      intro τ h1 h2 hτ
      have hmem : τ ∈ L := mem_stops_iff.2 ⟨lt_trans h2 (hlt k.succ), hτ⟩
      obtain ⟨m, hm⟩ : τ ∈ Set.range e := by
        rw [he, Finset.range_orderEmbOfFin]; exact hmem
      rw [← hm] at h1 h2
      have h3 : k.castSucc < m := e.lt_iff_lt.1 h1
      have h4 : m < k.succ := e.lt_iff_lt.1 h2
      have := Fin.lt_def.1 h3
      have := Fin.lt_def.1 h4
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      omega
    have := (lt_norm_sub_of_consecutive c θ hab (hfix k.castSucc) (hfix k.succ) hbetween).2
    rwa [norm_sub_rev] at this
  have hchain := hV M (fun k => e k) e.strictMono hlt
  have hMlt : (M : ℝ) * θ ^ s < lam ^ s := by
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · subst hM0
      simpa using Real.rpow_pos_of_pos hlam s
    · have : Nonempty (Fin M) := ⟨⟨0, hMpos⟩⟩
      calc (M : ℝ) * θ ^ s = ∑ _k : Fin M, θ ^ s := by simp
        _ < ∑ k : Fin M, ‖c (e k.castSucc) - c (e k.succ)‖ ^ s := by
          refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ => ?_
          exact Real.rpow_lt_rpow hθ.le (hsep k) hs
        _ ≤ lam ^ s := hchain
  have h2v : (0 : ℝ) < 2 ^ ((v : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  have hθs : θ ^ s = lam ^ s / 2 ^ ((v : ℝ) * s) := by
    rw [hθdef, Real.div_rpow hlam.le (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
  have hMlt2 : (M : ℝ) < 2 ^ ((v : ℝ) * s) := by
    rw [hθs, mul_div_assoc'] at hMlt
    rw [div_lt_iff₀ h2v] at hMlt
    rw [mul_comm (lam ^ s)] at hMlt
    exact lt_of_mul_lt_mul_right hMlt (Real.rpow_pos_of_pos hlam s).le
  rw [hM]
  push_cast
  linarith

/-- The union of the stopping times of two consecutive levels:
`U_v = Λ_v ∪ Λ_{v-1}` (for `v ≥ 1`), on which the level increment `D_v` is a step function. -/
def levelStops (c : ℕ → H) (lam : ℝ) (N v : ℕ) : Finset ℕ :=
  stops c (lam / 2 ^ v) N ∪ stops c (lam / 2 ^ (v - 1)) N

/-- **Counting for the step set**: for `v ≥ 1` and `s > 2`,
`|U_v| ≤ M_v + M_{v-1} + 1 < (3/2) 2^{v s}`.

Part of the chaining proof of main paper `l:entest` (L1824–L1860). -/
theorem card_levelStops_lt (hV : ChainBound c N s lam) (hs : 2 < s) (hlam : 0 < lam)
    (hN : 0 < N) {v : ℕ} (hv : 1 ≤ v) :
    ((levelStops c lam N v).card : ℝ) < 3 / 2 * (2 : ℝ) ^ ((v : ℝ) * s) := by
  have hs0 : 0 < s := by linarith
  set L1 := stops c (lam / 2 ^ v) N
  set L2 := stops c (lam / 2 ^ (v - 1)) N
  have h1 := card_stops_lt hV hs0 hlam hN v
  have h2 := card_stops_lt hV hs0 hlam hN (v - 1)
  have hinter : 1 ≤ (L1 ∩ L2).card :=
    Finset.card_pos.2 ⟨0, Finset.mem_inter.2 ⟨zero_mem_stops hN, zero_mem_stops hN⟩⟩
  have hcard := Finset.card_union_add_card_inter L1 L2
  have hU : ((L1 ∪ L2).card : ℝ) + 1 ≤ L1.card + L2.card := by
    have : (L1 ∪ L2).card + 1 ≤ L1.card + L2.card := by omega
    exact_mod_cast this
  change ((L1 ∪ L2).card : ℝ) < _
  have h2s : (4 : ℝ) < 2 ^ s := by
    calc (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
      _ < 2 ^ s := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs
  have hvs : (2 : ℝ) ^ s ≤ 2 ^ ((v : ℝ) * s) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have : (1 : ℝ) ≤ v := by exact_mod_cast hv
          nlinarith)
  have hv1 : (2 : ℝ) ^ (((v - 1 : ℕ) : ℝ) * s) = 2 ^ ((v : ℝ) * s) / 2 ^ s := by
    rw [← Real.rpow_sub (by norm_num)]
    congr 1
    rw [Nat.cast_sub hv]
    ring
  have hlow : (2 : ℝ) ^ ((v : ℝ) * s) / 4 < 2 ^ ((v : ℝ) * s) / 4 + 0 + 1 := by linarith
  have hq : (2 : ℝ) ^ ((v : ℝ) * s) / 2 ^ s < 2 ^ ((v : ℝ) * s) / 4 := by
    apply div_lt_div_of_pos_left (by positivity) (by norm_num) h2s
  have h44 : (4 : ℝ) < 2 ^ ((v : ℝ) * s) := lt_of_lt_of_le h2s hvs
  rw [hv1] at h2
  linarith

end ChainBound

end PrimeCarleson.Proof.Paper
