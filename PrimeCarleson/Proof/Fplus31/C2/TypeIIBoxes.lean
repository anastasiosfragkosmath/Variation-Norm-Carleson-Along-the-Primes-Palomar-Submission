module

public import PrimeCarleson.Proof.Fplus31.C2.TypeIGlue

/-!
# The type II step, first half: dilated boxes

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The input
is the type II conclusion of the Vaughan decomposition (`TypeIII/Main.lean`, `typeII_pairs`): for
`φ = 1_P · star (T.eval)` with `P = {n ∈ [lo, hi] : n ≡ r (q)}` the four-fold sum of `φ` over
`(L/2, L] × (M/2, M]` is at least `x N²`. `typeII_pairs` turns this into `≥ x L² / 32` pairs
`(ℓ, ℓ')` with `‖∑_{m ∈ (M/2, M]} φ (ℓ m) conj φ (ℓ' m)‖ ≥ x M / 8`, and the pigeonhole here, as in
the type I step (`C2/TypeI.lean`), picks one residue class `b` mod `q` and `≥ x L² / (32 q)` of the
pairs, each with a box of length `≥ x M / (8 q)` on which the product of the two stride-`q` dilated
pullbacks `m ↦ T.eval (ℓ (b + q m)) · conj (T.eval (ℓ' (b + q m)))` has bias `≥ x / 16`. This is the
input of the engine on the product model `D × D` (`C2/TypeIIEngine.lean`).

* `eq_Icc_min'_max'`: a convex finite set of integers is an interval;
* `pairTerm`, `sum_dyadicBlock_eq_int`, `class_sum_pair`: on a residue class the pair sum is a sum
  over an interval of `m` (the progression and the block cut-off are three interval conditions);
* `type_two_core`: the pigeonhole over the pairs and the length bounds for a bounded `v : ℤ → ℂ`;
* `type_two_boxes`: the statement for a one-variable niltest `T` with `‖T‖ ≤ 1`.

The hypothesis `q ≤ M` holds in the application (`q³ ≤ N < M³`).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators ComplexConjugate

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Finset

/-- A finite set of integers that is convex is the interval between its extremes. -/
theorem eq_Icc_min'_max' (S : Finset ℤ) (hne : S.Nonempty)
    (hconv : ∀ a ∈ S, ∀ c ∈ S, ∀ m : ℤ, a ≤ m → m ≤ c → m ∈ S) :
    S = Finset.Icc (S.min' hne) (S.max' hne) := by
  ext m
  rw [Finset.mem_Icc]
  constructor
  · intro hm
    exact ⟨Finset.min'_le S m hm, Finset.le_max' S m hm⟩
  · rintro ⟨h1, h2⟩
    exact hconv _ (Finset.min'_mem S hne) _ (Finset.max'_mem S hne) m h1 h2

/-- The term `1_P(ℓ n) v(ℓ n) conj (1_P(ℓ' n) v(ℓ' n))` of the type II sum. -/
def pairTerm (q : ℕ) (r lo hi : ℤ) (v : ℤ → ℂ) (ℓ ℓ' : ℕ) (n : ℤ) : ℂ :=
  (progIndicator q r lo hi ((ℓ : ℤ) * n) * v ((ℓ : ℤ) * n)) *
    (starRingEnd ℂ) (progIndicator q r lo hi ((ℓ' : ℤ) * n) * v ((ℓ' : ℤ) * n))

/-- The progression indicator is real: it is its own conjugate. -/
theorem conj_progIndicator (q : ℕ) (r lo hi n : ℤ) :
    (starRingEnd ℂ) (progIndicator q r lo hi n) = progIndicator q r lo hi n := by
  unfold progIndicator
  split_ifs <;> simp

/-- The sum over the dyadic block as a sum over `[1, M] ⊆ ℤ` with the block cut-off. -/
theorem sum_dyadicBlock_eq_int (g : ℤ → ℂ) (M : ℕ) :
    ∑ m ∈ dyadicBlock M, g (m : ℤ) =
      ∑ n ∈ Finset.Icc (1 : ℤ) M, if ((M / 2 : ℕ) : ℤ) < n then g n else 0 := by
  rw [← sum_Icc_natCast_eq_int (fun n : ℤ => if ((M / 2 : ℕ) : ℤ) < n then g n else 0) M,
    ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun n _ => ?_
  · ext n
    simp only [dyadicBlock, Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, h2⟩, by exact_mod_cast h1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by exact_mod_cast h3, h2⟩
  · rfl


/-- The pair term as a product of two indicators and `v (ℓ n) conj (v (ℓ' n))`. -/
theorem pairTerm_eq (q : ℕ) (r lo hi : ℤ) (v : ℤ → ℂ) (ℓ ℓ' : ℕ) (n : ℤ) :
    pairTerm q r lo hi v ℓ ℓ' n = progIndicator q r lo hi ((ℓ : ℤ) * n) *
      progIndicator q r lo hi ((ℓ' : ℤ) * n) *
        (v ((ℓ : ℤ) * n) * (starRingEnd ℂ) (v ((ℓ' : ℤ) * n))) := by
  unfold pairTerm
  rw [map_mul, conj_progIndicator]
  ring

/-- On a residue class `n = q m + b` with a nonzero block-cut-off pair sum, the pair sum is a sum
over an interval of `m`. -/
theorem class_sum_pair (v : ℤ → ℂ) {q : ℕ} (hq : 1 ≤ q) (r lo hi : ℤ) {ℓ ℓ' : ℕ}
    (hℓ : 1 ≤ ℓ) (hℓ' : 1 ≤ ℓ') {M : ℕ} {b : ℤ} (hb0 : 0 ≤ b) (hbq : b < q)
    (hZ : ∑ m ∈ residueSet q M b, (if ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b then
      pairTerm q r lo hi v ℓ ℓ' ((q : ℤ) * m + b) else 0) ≠ 0) :
    ∃ u w : ℤ, u ≤ w ∧ ((M / 2 : ℕ) : ℤ) < (q : ℤ) * u + b ∧ (q : ℤ) * w + b ≤ M ∧
      ∑ m ∈ residueSet q M b, (if ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b then
        pairTerm q r lo hi v ℓ ℓ' ((q : ℤ) * m + b) else 0) =
      ∑ m ∈ Finset.Icc u w, v ((ℓ : ℤ) * b + (ℓ : ℤ) * q * m) *
        (starRingEnd ℂ) (v ((ℓ' : ℤ) * b + (ℓ' : ℤ) * q * m)) := by
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hℓ1 : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ1' : (1 : ℤ) ≤ ℓ' := by exact_mod_cast hℓ'
  have hmod : ∀ (k : ℕ) (m : ℤ), (k : ℤ) * (q * m + b) ≡ (k : ℤ) * b [ZMOD q] := by
    intro k m
    rw [Int.modEq_iff_dvd]
    exact ⟨-((k : ℤ) * m), by ring⟩
  by_cases hc : (ℓ : ℤ) * b ≡ r [ZMOD q] ∧ (ℓ' : ℤ) * b ≡ r [ZMOD q]
  swap
  · exfalso
    apply hZ
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [pairTerm_eq]
    by_cases h1 : (ℓ : ℤ) * b ≡ r [ZMOD q]
    · have h2 : ¬ (ℓ' : ℤ) * b ≡ r [ZMOD q] := fun h => hc ⟨h1, h⟩
      have : ¬ (ℓ' : ℤ) * (q * m + b) ≡ r [ZMOD q] := fun h => h2 ((hmod ℓ' m).symm.trans h)
      simp [progIndicator, this]
    · have : ¬ (ℓ : ℤ) * (q * m + b) ≡ r [ZMOD q] := fun h => h1 ((hmod ℓ m).symm.trans h)
      simp [progIndicator, this]
  obtain ⟨hc1, hc2⟩ := hc
  have hind : ∀ (k : ℕ), (k : ℤ) * b ≡ r [ZMOD q] → ∀ m : ℤ,
      progIndicator q r lo hi ((k : ℤ) * (q * m + b)) =
        if lo ≤ (k : ℤ) * (q * m + b) ∧ (k : ℤ) * (q * m + b) ≤ hi then 1 else 0 := by
    intro k hk m
    have h1 : (k : ℤ) * (q * m + b) ≡ r [ZMOD q] := (hmod k m).trans hk
    simp only [progIndicator, h1, and_true]
  obtain ⟨M', hM'⟩ : ∃ M' : Finset ℤ, M' = (residueSet q M b).filter
    (fun m => ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b ∧
      (lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi) ∧
      (lo ≤ (ℓ' : ℤ) * (q * m + b) ∧ (ℓ' : ℤ) * (q * m + b) ≤ hi)) := ⟨_, rfl⟩
  have hmem : ∀ m, m ∈ M' ↔ (1 ≤ (q : ℤ) * m + b ∧ (q : ℤ) * m + b ≤ M) ∧
      ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b ∧
      (lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi) ∧
      (lo ≤ (ℓ' : ℤ) * (q * m + b) ∧ (ℓ' : ℤ) * (q * m + b) ≤ hi) := by
    intro m
    rw [hM', Finset.mem_filter, mem_residueSet hq hb0 hbq]
  have hsum : ∑ m ∈ residueSet q M b, (if ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b then
        pairTerm q r lo hi v ℓ ℓ' ((q : ℤ) * m + b) else 0) =
      ∑ m ∈ M', v ((ℓ : ℤ) * (q * m + b)) * (starRingEnd ℂ) (v ((ℓ' : ℤ) * (q * m + b))) := by
    rw [hM', Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [pairTerm_eq, hind ℓ hc1 m, hind ℓ' hc2 m]
    by_cases h0 : ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b
    · by_cases h1 : lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi
      · by_cases h2 : lo ≤ (ℓ' : ℤ) * (q * m + b) ∧ (ℓ' : ℤ) * (q * m + b) ≤ hi
        · have hc : ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b ∧
              (lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi) ∧
              (lo ≤ (ℓ' : ℤ) * (q * m + b) ∧ (ℓ' : ℤ) * (q * m + b) ≤ hi) := ⟨h0, h1, h2⟩
          rw [ite_eq_left h0, ite_eq_left h1, ite_eq_left h2, ite_eq_left hc]
          simp
        · have hc : ¬ (((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b ∧
              (lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi) ∧
              (lo ≤ (ℓ' : ℤ) * (q * m + b) ∧ (ℓ' : ℤ) * (q * m + b) ≤ hi)) := fun h => h2 h.2.2
          rw [ite_eq_left h0, ite_eq_right h2, ite_eq_right hc]
          simp
      · have hc : ¬ (((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b ∧
              (lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi) ∧
              (lo ≤ (ℓ' : ℤ) * (q * m + b) ∧ (ℓ' : ℤ) * (q * m + b) ≤ hi)) := fun h => h1 h.2.1
        rw [ite_eq_left h0, ite_eq_right h1, ite_eq_right hc]
        simp
    · have hc : ¬ (((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b ∧
              (lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi) ∧
              (lo ≤ (ℓ' : ℤ) * (q * m + b) ∧ (ℓ' : ℤ) * (q * m + b) ≤ hi)) := fun h => h0 h.1
      rw [ite_eq_right h0, ite_eq_right hc]
  have hne : M'.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [hsum, h, Finset.sum_empty] at hZ
    exact hZ rfl
  have hu := (hmem _).mp (Finset.min'_mem M' hne)
  have hw := (hmem _).mp (Finset.max'_mem M' hne)
  have huw : M'.min' hne ≤ M'.max' hne := Finset.min'_le_max' M' hne
  have hIcc : M' = Finset.Icc (M'.min' hne) (M'.max' hne) := by
    refine eq_Icc_min'_max' M' hne ?_
    intro a ha c hc' m ham hmc
    rw [hmem] at ha hc' ⊢
    obtain ⟨⟨ha1, ha1'⟩, ha2, ⟨ha3, ha3'⟩, ⟨ha4, ha4'⟩⟩ := ha
    obtain ⟨⟨hc1', hc1''⟩, hc2', ⟨hc3, hc3'⟩, ⟨hc4, hc4'⟩⟩ := hc'
    have e1 : (q : ℤ) * a ≤ q * m := mul_le_mul_of_nonneg_left ham (by omega)
    have e2 : (q : ℤ) * m ≤ q * c := mul_le_mul_of_nonneg_left hmc (by omega)
    have e3 : (ℓ : ℤ) * (q * a + b) ≤ ℓ * (q * m + b) :=
      mul_le_mul_of_nonneg_left (by linarith only [e1]) (by omega)
    have e4 : (ℓ : ℤ) * (q * m + b) ≤ ℓ * (q * c + b) :=
      mul_le_mul_of_nonneg_left (by linarith only [e2]) (by omega)
    have e5 : (ℓ' : ℤ) * (q * a + b) ≤ ℓ' * (q * m + b) :=
      mul_le_mul_of_nonneg_left (by linarith only [e1]) (by omega)
    have e6 : (ℓ' : ℤ) * (q * m + b) ≤ ℓ' * (q * c + b) :=
      mul_le_mul_of_nonneg_left (by linarith only [e2]) (by omega)
    exact ⟨⟨by linarith only [ha1, e1], by linarith only [e2, hc1'']⟩, by linarith only [ha2, e1],
      ⟨by linarith only [ha3, e3], by linarith only [e4, hc3']⟩,
      ⟨by linarith only [ha4, e5], by linarith only [e6, hc4']⟩⟩
  refine ⟨M'.min' hne, M'.max' hne, huw, hu.2.1, hw.1.2, ?_⟩
  rw [hsum]
  conv_lhs => rw [hIcc]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 3 <;> ring


/-- **The type II step, the combinatorial core.**  For a function `v` bounded by one, the pair sums
`∑_{m ∈ (M/2, M]} 1_P(ℓ m) v(ℓ m) conj (1_P(ℓ' m) v(ℓ' m))` of norm `≥ θ` for the pairs of `Γ` give
a residue class `b` mod `q` and `≥ |Γ| / q` of the pairs with a box `[o, o + len)`,
`len ≥ θ / q`, on which `‖∑_m v(ℓ (b + q m)) conj v(ℓ' (b + q m))‖ ≥ (θ / (2 M)) len`
(needs `q ≤ M`). -/
theorem type_two_core (v : ℤ → ℂ) (hv : ∀ n, ‖v n‖ ≤ 1) {q : ℕ} (hq : 1 ≤ q) (r lo hi : ℤ)
    {M : ℕ} (hM : 1 ≤ M) (hqM : q ≤ M) {θ : ℝ} (hθ : 0 < θ) {Γ : Finset (ℕ × ℕ)}
    (hΓ : ∀ pr ∈ Γ, 1 ≤ pr.1 ∧ 1 ≤ pr.2)
    (hsum : ∀ pr ∈ Γ, θ ≤ ‖∑ m ∈ dyadicBlock M, pairTerm q r lo hi v pr.1 pr.2 (m : ℤ)‖) :
    ∃ b : ℤ, ∃ Γ' ⊆ Γ, (Γ.card : ℝ) / q ≤ Γ'.card ∧ ∀ pr ∈ Γ', ∃ (o : ℤ) (len : ℕ),
      θ / q ≤ len ∧ θ / (2 * M) * len ≤ ‖∑ m ∈ Finset.Ico o (o + len),
        v ((pr.1 : ℤ) * b + (pr.1 : ℤ) * q * m) *
          (starRingEnd ℂ) (v ((pr.2 : ℤ) * b + (pr.2 : ℤ) * q * m))‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  -- the residue class of each pair
  have hex : ∀ pr : ℕ × ℕ, ∃ b : ℤ, pr ∈ Γ → (b ∈ Finset.Ico (0 : ℤ) q ∧
      θ / q ≤ ‖∑ m ∈ residueSet q M b, (if ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b then
        pairTerm q r lo hi v pr.1 pr.2 ((q : ℤ) * m + b) else 0)‖) := by
    intro pr
    by_cases hpr : pr ∈ Γ
    · obtain ⟨b, hb, h⟩ := exists_residue_norm_ge
        (fun n : ℤ => if ((M / 2 : ℕ) : ℤ) < n then pairTerm q r lo hi v pr.1 pr.2 n else 0)
        hq (M : ℤ)
      refine ⟨b, fun _ => ⟨hb, ?_⟩⟩
      have h1 := hsum pr hpr
      rw [sum_dyadicBlock_eq_int (fun n : ℤ => pairTerm q r lo hi v pr.1 pr.2 n) M] at h1
      exact (div_le_div_of_nonneg_right h1 hq0.le).trans h
    · exact ⟨0, fun h => absurd h hpr⟩
  choose β hβ using hex
  have hmaps : ∀ pr ∈ Γ, β pr ∈ Finset.Ico (0 : ℤ) q := fun pr hpr => (hβ pr hpr).1
  have hne : (Finset.Ico (0 : ℤ) q).Nonempty := ⟨0, by rw [Finset.mem_Ico]; omega⟩
  have hcardIco : ((Finset.Ico (0 : ℤ) q).card : ℝ) = q := by
    rw [Int.card_Ico]
    simp
  obtain ⟨b₀, hb₀, hfib⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (b := (Γ.card : ℝ) / q) hmaps hne (by
      rw [nsmul_eq_mul, hcardIco, mul_div_cancel₀ _ hq0.ne'])
  refine ⟨b₀, Γ.filter (fun pr => β pr = b₀), Finset.filter_subset _ _, hfib, ?_⟩
  intro pr hpr'
  rw [Finset.mem_filter] at hpr'
  obtain ⟨hpr, hβpr⟩ := hpr'
  obtain ⟨hbmem, hbound⟩ := hβ pr hpr
  rw [hβpr] at hbmem hbound
  rw [Finset.mem_Ico] at hbmem
  obtain ⟨hb0, hbq⟩ := hbmem
  obtain ⟨h1, h2⟩ := hΓ pr hpr
  have hZne : ∑ m ∈ residueSet q M b₀, (if ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b₀ then
      pairTerm q r lo hi v pr.1 pr.2 ((q : ℤ) * m + b₀) else 0) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hbound
    have : 0 < θ / q := by positivity
    linarith
  obtain ⟨u, w, huw, hu1, hw1, hZeq⟩ := class_sum_pair v hq r lo hi h1 h2 hb0 hbq hZne
  have hlen : (((w + 1 - u).toNat : ℕ) : ℤ) = w + 1 - u := Int.toNat_of_nonneg (by omega)
  have hIco : Finset.Ico u (u + (((w + 1 - u).toNat : ℕ) : ℤ)) = Finset.Icc u w := by
    ext m
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  refine ⟨u, (w + 1 - u).toNat, ?_⟩
  rw [hIco, ← hZeq]
  have hZle : ‖∑ m ∈ residueSet q M b₀, (if ((M / 2 : ℕ) : ℤ) < (q : ℤ) * m + b₀ then
        pairTerm q r lo hi v pr.1 pr.2 ((q : ℤ) * m + b₀) else 0)‖ ≤
      (((w + 1 - u).toNat : ℕ) : ℝ) := by
    rw [hZeq]
    calc ‖∑ m ∈ Finset.Icc u w, v ((pr.1 : ℤ) * b₀ + (pr.1 : ℤ) * q * m) *
          (starRingEnd ℂ) (v ((pr.2 : ℤ) * b₀ + (pr.2 : ℤ) * q * m))‖
        ≤ ∑ m ∈ Finset.Icc u w, (1 : ℝ) := by
          refine norm_sum_le_of_le _ (fun m _ => ?_)
          rw [norm_mul, Complex.norm_conj]
          calc ‖v ((pr.1 : ℤ) * b₀ + (pr.1 : ℤ) * q * m)‖ *
              ‖v ((pr.2 : ℤ) * b₀ + (pr.2 : ℤ) * q * m)‖ ≤ 1 * 1 :=
                mul_le_mul (hv _) (hv _) (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = (((w + 1 - u).toNat : ℕ) : ℝ) := by
          rw [Finset.sum_const, Int.card_Icc]
          simp
  refine ⟨hbound.trans hZle, ?_⟩
  -- the upper bound on the length
  have hlenZ : (q : ℤ) * (((w + 1 - u).toNat : ℕ) : ℤ) ≤ 2 * M := by
    rw [hlen]
    have hqM' : (q : ℤ) ≤ M := by exact_mod_cast hqM
    have hdiv : (0 : ℤ) ≤ ((M / 2 : ℕ) : ℤ) := Nat.cast_nonneg _
    linarith only [hu1, hw1, hqM', hdiv]
  have hlenR : (q : ℝ) * (((w + 1 - u).toNat : ℕ) : ℝ) ≤ 2 * M := by
    exact_mod_cast hlenZ
  have hlen' : (((w + 1 - u).toNat : ℕ) : ℝ) ≤ 2 * M / q := by
    rw [le_div_iff₀ hq0]
    linarith
  calc θ / (2 * M) * (((w + 1 - u).toNat : ℕ) : ℝ) ≤ θ / (2 * M) * (2 * M / q) :=
        mul_le_mul_of_nonneg_left hlen' (by positivity)
    _ = θ / q := by field_simp
    _ ≤ _ := hbound


section Niltest

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

/-- **The type II step: dilated boxes** (Leng23 Prop 5.4, `Final_Version.tex` L1154-L1181). Let `T`
be a one-variable niltest with `‖T‖ ≤ 1`, `P = {n ∈ [lo, hi] : n ≡ r (q)}` and
`φ = 1_P · star (T.eval)`. If the four-fold sum of `φ` over `(L/2, L] × (M/2, M]` is at least `x N²`
(the type II output of the Vaughan decomposition) with `L M < 4 N`, `0 < x ≤ 1` and `q ≤ M`, then
there are a class `b` mod `q` and `≥ x L² / (32 q)` pairs `(ℓ, ℓ') ∈ (L/2, L]²`, each with a box
`[o, o + len)` of length `≥ x M / (8 q)` on which the product of the pullbacks
`m ↦ T.eval (ℓ b + ℓ q m) · conj (T.eval (ℓ' b + ℓ' q m))` has bias `≥ x / 16`. -/
theorem type_two_boxes (T : D.Niltest (fun _ : Unit => 1)) (hT : (T.normBound : ℝ) ≤ 1)
    {q : ℕ} (hq : 1 ≤ q) (r lo hi : ℤ) {N L M : ℕ} (hM : 1 ≤ M) (hqM : q ≤ M)
    (hLM : (L : ℝ) * M < 4 * N) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hF : x * (N : ℝ) ^ 2 ≤
      fourFold (fun n : ℕ => typeISequence T q r lo hi (n : ℤ)) (dyadicBlock L) (dyadicBlock M)) :
    ∃ b : ℤ, ∃ Γ ⊆ dyadicBlock L ×ˢ dyadicBlock L, x / 32 * (L : ℝ) ^ 2 / q ≤ Γ.card ∧
      ∀ pr ∈ Γ, ∃ (o : ℤ) (len : ℕ), x * M / (8 * q) ≤ len ∧ x / 16 ≤
        ‖𝔼 m ∈ translatedIntegerBox (fun _ : Unit => o) (fun _ : Unit => len),
          (T.affinePullback (fun (_ : Unit) (_ : Unit) => (pr.1 : ℤ) * (q : ℤ))
            (fun _ : Unit => (pr.1 : ℤ) * b)).eval m *
          star ((T.affinePullback (fun (_ : Unit) (_ : Unit) => (pr.2 : ℤ) * (q : ℤ))
            (fun _ : Unit => (pr.2 : ℤ) * b)).eval m)‖ := by
  have hf : ∀ n : ℕ, ‖typeISequence T q r lo hi (n : ℤ)‖ ≤ 1 := fun n =>
    norm_typeISequence_le T hT q r lo hi _
  obtain ⟨P, hP, hcard, hval⟩ := typeII_pairs (fun n : ℕ => typeISequence T q r lo hi (n : ℤ)) hf
    hM hx0 hx1 hLM hF
  have hv : ∀ n : ℤ, ‖star (T.eval fun _ : Unit => n)‖ ≤ 1 := fun n => by
    rw [norm_star]
    exact (T.norm_eval_le _).trans hT
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hΓ : ∀ pr ∈ P, 1 ≤ pr.1 ∧ 1 ≤ pr.2 := by
    intro pr hpr
    have h := Finset.mem_product.mp (hP hpr)
    simp only [dyadicBlock, Finset.mem_Ioc] at h
    omega
  obtain ⟨b, Γ', hsub, hcard', hbox⟩ := type_two_core (fun n : ℤ => star (T.eval fun _ : Unit => n))
    hv hq r lo hi hM hqM (θ := x / 8 * M) (by positivity) hΓ (fun pr hpr => by
      refine (hval pr hpr).trans (le_of_eq ?_)
      congr 2)
  refine ⟨b, Γ', fun pr hpr => hP (hsub hpr), ?_, fun pr hpr => ?_⟩
  · refine le_trans ?_ hcard'
    exact div_le_div_of_nonneg_right hcard hq0.le
  obtain ⟨o, len, hlen, hmean⟩ := hbox pr hpr
  refine ⟨o, len, ?_, ?_⟩
  · have : x / 8 * M / q = x * M / (8 * q) := by field_simp
    rwa [this] at hlen
  have hY : 0 < x * M / (8 * q) := by positivity
  have hlen0 : 0 < len := by
    have : (0 : ℝ) < len := lt_of_lt_of_le hY (by
      have : x / 8 * M / q = x * M / (8 * q) := by field_simp
      rwa [this] at hlen)
    exact_mod_cast this
  rw [expect_translatedIntegerBox_unit o len hlen0, norm_mul, norm_inv, Complex.norm_natCast]
  have hsumeq : ‖∑ m ∈ Finset.Ico o (o + len),
      (T.affinePullback (fun (_ : Unit) (_ : Unit) => (pr.1 : ℤ) * (q : ℤ))
        (fun _ : Unit => (pr.1 : ℤ) * b)).eval (fun _ => m) *
      star ((T.affinePullback (fun (_ : Unit) (_ : Unit) => (pr.2 : ℤ) * (q : ℤ))
        (fun _ : Unit => (pr.2 : ℤ) * b)).eval (fun _ => m))‖ =
      ‖∑ m ∈ Finset.Ico o (o + len),
        star (T.eval fun _ : Unit => (pr.1 : ℤ) * b + (pr.1 : ℤ) * q * m) *
          (starRingEnd ℂ) (star (T.eval fun _ : Unit => (pr.2 : ℤ) * b + (pr.2 : ℤ) * q * m))‖ := by
    rw [← norm_star, star_sum]
    refine congrArg (fun z : ℂ => ‖z‖) ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [affinePullback_unit_eval, affinePullback_unit_eval]
    simp [star_mul']
  rw [hsumeq]
  have hlenR : (0 : ℝ) < len := by exact_mod_cast hlen0
  rw [inv_mul_eq_div, le_div_iff₀ hlenR]
  have : x / 8 * M / (2 * M) = x / 16 := by field_simp; ring
  rw [this] at hmean
  exact hmean

end Niltest

end PrimeCarleson.Proof.Fplus31
