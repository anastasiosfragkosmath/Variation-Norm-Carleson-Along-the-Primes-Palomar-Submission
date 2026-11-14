module

public import PrimeCarleson.Proof.Paper.P8.Nets
public import PrimeCarleson.Proof.Paper.P8.Chain

/-!
# Level increments and the chain bound for the entropy lemma

Part of the chaining proof of main paper `l:entest` (L1824–L1860): the level increments and the
chain bound.

For `v ≥ 1` the level increment `D_v(j) := c_{π_v(j)} - c_{π_{v-1}(j)}` (`levelIncrement`, with
`π_v = net c (λ 2^{-v})`) is defined for every index `j`, not only for stopping times:

* `norm_levelIncrement_le`: `‖D_v(j)‖ ≤ 3 λ 2^{-v}`;
* `levelRetract`, `levelIncrement_levelRetract`: the function `j ↦ max(π_v(j), π_{v-1}(j))` is a
  monotone retraction of `[0, N)` onto `U_v := Λ_v ∪ Λ_{v-1}` with `D_v(j) = D_v(retract j)` (the
  step structure of `D_v`), the form that Lemma S (`rVariationOnH_le_two_mul_of_retraction`)
  consumes;
* `exists_exhaust`: for a threshold `λ 2^{-V₀}` small enough, `c_{π_{V₀}(j)} = c_j`;
* `c_eq_telescope`: the exact finite telescoping `c_{π_V(j)} = c_0 + ∑_{v=1}^V D_v(j)`;
* `chain_variation_le_levels`: for an additive functional `φ` (the pairing with `g(y)`) and an
  index chain, `(∑_k ‖φ c_{j_k} - φ c_{j_{k+1}}‖^r)^{1/r} ≤ 2 ∑_{v=1}^{V₀} F_v` with
  `F_v = (∑_{u ∈ U_v} ‖φ D_v(u)‖^r)^{1/r}`.
-/

@[expose] public noncomputable section

open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

variable {H : Type*} [NormedAddCommGroup H]

/-- The level-`v` increment `D_v(j) = c_{π_v(j)} - c_{π_{v-1}(j)}`, a function of every index `j`
(not only of the stopping times of level `v`). -/
def levelIncrement (c : ℕ → H) (lam : ℝ) (v j : ℕ) : H :=
  c (net c (lam / 2 ^ v) j) - c (net c (lam / 2 ^ (v - 1)) j)

/-- The monotone retraction `j ↦ max (π_v j) (π_{v-1} j)` of `[0, N)` onto `U_v`. -/
def levelRetract (c : ℕ → H) (lam : ℝ) (v j : ℕ) : ℕ :=
  max (net c (lam / 2 ^ v) j) (net c (lam / 2 ^ (v - 1)) j)

variable {c : ℕ → H} {lam : ℝ}

/-- Size of the increments: `‖D_v(j)‖ ≤ 3 λ 2^{-v}` for `v ≥ 1`. -/
theorem norm_levelIncrement_le (hlam : 0 ≤ lam) {v : ℕ} (hv : 1 ≤ v) (j : ℕ) :
    ‖levelIncrement c lam v j‖ ≤ 3 * (lam / 2 ^ v) := by
  have h1 := norm_sub_net_le c (lam / 2 ^ v) (by positivity) j
  have h2 := norm_sub_net_le c (lam / 2 ^ (v - 1)) (by positivity) j
  have h3 : lam / 2 ^ (v - 1) = 2 * (lam / 2 ^ v) := by
    obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  calc ‖levelIncrement c lam v j‖
      = ‖(c (net c (lam / 2 ^ v) j) - c j) + (c j - c (net c (lam / 2 ^ (v - 1)) j))‖ := by
        simp [levelIncrement]
    _ ≤ ‖c (net c (lam / 2 ^ v) j) - c j‖ + ‖c j - c (net c (lam / 2 ^ (v - 1)) j)‖ :=
        norm_add_le _ _
    _ ≤ lam / 2 ^ v + lam / 2 ^ (v - 1) := by
        rw [norm_sub_rev (c (net c (lam / 2 ^ v) j))]
        exact add_le_add h1 h2
    _ = 3 * (lam / 2 ^ v) := by rw [h3]; ring

/-- `levelRetract` is monotone. -/
theorem monotone_levelRetract (v : ℕ) : Monotone (levelRetract c lam v) := fun _ _ h =>
  max_le_max (monotone_net c _ h) (monotone_net c _ h)

/-- `levelRetract j ∈ U_v` for `j < N`. -/
theorem levelRetract_mem {N v j : ℕ} (hj : j < N) :
    levelRetract c lam v j ∈ levelStops c lam N v := by
  unfold levelRetract levelStops
  rcases max_choice (net c (lam / 2 ^ v) j) (net c (lam / 2 ^ (v - 1)) j) with h | h
  · rw [h]; exact Finset.mem_union_left _ (net_mem_stops hj)
  · rw [h]; exact Finset.mem_union_right _ (net_mem_stops hj)

/-- `D_v(j)` only depends on the retract of `j`: `D_v(retract j) = D_v(j)`. -/
theorem levelIncrement_levelRetract (v j : ℕ) :
    levelIncrement c lam v (levelRetract c lam v j) = levelIncrement c lam v j := by
  have hle : levelRetract c lam v j ≤ j :=
    max_le (net_le_self c _ j) (net_le_self c _ j)
  have e1 : net c (lam / 2 ^ v) (levelRetract c lam v j) = net c (lam / 2 ^ v) j :=
    net_eq_of_between c _ (le_max_left _ _) hle
  have e2 : net c (lam / 2 ^ (v - 1)) (levelRetract c lam v j) =
      net c (lam / 2 ^ (v - 1)) j :=
    net_eq_of_between c _ (le_max_right _ _) hle
  unfold levelIncrement
  rw [e1, e2]

/-- **Exhaustion**: for `λ > 0` there is `V₀` such that the net of
threshold `λ 2^{-V₀}` reproduces `c` on `[0, N)`: `c_{π_{V₀}(j)} = c_j`. -/
theorem exists_exhaust (hlam : 0 < lam) (N : ℕ) :
    ∃ V₀ : ℕ, ∀ j < N, c (net c (lam / 2 ^ V₀) j) = c j := by
  have hpair : ∀ p : ℕ × ℕ, ∃ V : ℕ, c p.1 ≠ c p.2 → lam / 2 ^ V < ‖c p.1 - c p.2‖ := by
    intro p
    by_cases h : c p.1 = c p.2
    · exact ⟨0, fun h' => absurd h h'⟩
    · have hd : 0 < ‖c p.1 - c p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
      obtain ⟨V, hV⟩ := exists_nat_gt (lam / ‖c p.1 - c p.2‖)
      refine ⟨V, fun _ => ?_⟩
      have h2V : (V : ℝ) < 2 ^ V := by exact_mod_cast Nat.lt_two_pow_self
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hd] at hV
      nlinarith
  choose V hV using hpair
  refine ⟨(Finset.range N ×ˢ Finset.range N).sup V, fun j hj => ?_⟩
  set V₀ := (Finset.range N ×ˢ Finset.range N).sup V with hV₀
  by_contra hne
  have hle := norm_sub_net_le c (lam / 2 ^ V₀) (by positivity) j
  have hjn : net c (lam / 2 ^ V₀) j < N := lt_of_le_of_lt (net_le_self c _ j) hj
  have hp : (j, net c (lam / 2 ^ V₀) j) ∈ Finset.range N ×ˢ Finset.range N := by
    simp [hj, hjn]
  have hVp : V (j, net c (lam / 2 ^ V₀) j) ≤ V₀ := Finset.le_sup (f := V) hp
  have hlt := hV (j, net c (lam / 2 ^ V₀) j) (fun h => hne h.symm)
  have hmono : lam / 2 ^ V₀ ≤ lam / 2 ^ V (j, net c (lam / 2 ^ V₀) j) :=
    div_le_div_of_nonneg_left hlam.le (by positivity) (pow_le_pow_right₀ (by norm_num) hVp)
  simp only at hlt
  linarith

/-- **Telescoping**: under (V), for `j < N` and every `V`,
`c_{π_V(j)} = c_0 + ∑_{v=1}^V D_v(j)` (the level-0 net is trivial). -/
theorem c_eq_telescope {N : ℕ} {s : ℝ} (hV : ChainBound c N s lam) (hs : 0 < s) (hlam : 0 ≤ lam)
    {j : ℕ} (hj : j < N) (V : ℕ) :
    c (net c (lam / 2 ^ V) j) = c 0 + ∑ v ∈ Finset.Icc 1 V, levelIncrement c lam v j := by
  induction V with
  | zero => simp [net_eq_zero_of_chainBound hV hs hlam hj]
  | succ V ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    simp [levelIncrement]

/-- **Chain bound** (a step of the chaining proof of `l:entest`): let `φ` be additive (the
pairing with `g(y)`), `V₀` as in `exists_exhaust`, and `j₀ < ⋯ < j_K < N` an index chain. Then for
`1 ≤ r`,

`(∑_k ‖φ c_{j_k} - φ c_{j_{k+1}}‖^r)^{1/r} ≤ 2 ∑_{v=1}^{V₀} (∑_{u∈U_v} ‖φ D_v(u)‖^r)^{1/r}`. -/
theorem chain_variation_le_levels (φ : H →+ ℂ) {N : ℕ} {s : ℝ} (hV : ChainBound c N s lam)
    (hs : 0 < s) (hlam : 0 ≤ lam) {V₀ : ℕ} (hex : ∀ j < N, c (net c (lam / 2 ^ V₀) j) = c j)
    {r : ℝ} (hr : 1 ≤ r) {K : ℕ} {j : Fin (K + 1) → ℕ} (hjm : StrictMono j)
    (hjN : ∀ k, j k < N) :
    (∑ k : Fin K, ‖φ (c (j k.castSucc)) - φ (c (j k.succ))‖ₑ ^ r) ^ (1 / r) ≤
      2 * ∑ v ∈ Finset.Icc 1 V₀,
        (∑ u ∈ levelStops c lam N v, ‖φ (levelIncrement c lam v u)‖ₑ ^ r) ^ (1 / r) := by
  have hφ : ∀ i < N, φ (c i) = φ (c 0) + ∑ v ∈ Finset.Icc 1 V₀, φ (levelIncrement c lam v i) := by
    intro i hi
    rw [← map_sum, ← map_add, ← c_eq_telescope hV hs hlam hi V₀, hex i hi]
  set x : ℕ → Fin K → ℂ := fun v k =>
    φ (levelIncrement c lam v (j k.castSucc)) - φ (levelIncrement c lam v (j k.succ)) with hx
  have hdiff : ∀ k : Fin K, φ (c (j k.castSucc)) - φ (c (j k.succ)) =
      ∑ v ∈ Finset.Icc 1 V₀, x v k := by
    intro k
    rw [hφ _ (hjN _), hφ _ (hjN _), hx]
    simp only [Finset.sum_sub_distrib]
    ring
  have h1 : (∑ k : Fin K, ‖φ (c (j k.castSucc)) - φ (c (j k.succ))‖ₑ ^ r) ^ (1 / r) =
      (∑ k : Fin K, ‖∑ v ∈ Finset.Icc 1 V₀, x v k‖ₑ ^ r) ^ (1 / r) := by
    simp only [hdiff]
  rw [h1]
  refine (Lp_enorm_sum_le_sum Finset.univ (Finset.Icc 1 V₀) x hr).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have hb : Monotone fun k => levelRetract c lam v (j k) :=
    fun k k' h => monotone_levelRetract v (hjm.monotone h)
  have := chain_variation_le_two_mul hb (fun u => φ (levelIncrement c lam v u))
    (levelStops c lam N v) (fun k => levelRetract_mem (hjN k)) hr (K := K)
  simpa only [hx, levelIncrement_levelRetract] using this

end PrimeCarleson.Proof.Paper
