module

public import PrimeCarleson.Proof.Fplus31.G1.Dilation
public import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

/-!
# The type I step, dilated boxes

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The input
is the type I conclusion of the Vaughan decomposition (`TypeIII/Main.lean`,
`vonMangoldt_sub_cramer_typeI_or_typeII`): for `φ = 1_P · star (T.eval)`,
`P = {n ∈ [lo, hi] : n ≡ r (q)}`, a cut-off `N' ≤ N`, a scale `L` and `≥ δ L` integers
`ℓ ∈ (L/2, L]` with `‖∑_{n ≤ ⌊N'/ℓ⌋} φ(ℓ n)‖ ≥ δ N / L` (`hsum` below). The output is Leng's
pigeonhole: one residue class `b` mod `q` and `≥ δ L / q` of the `ℓ`, each with a box of length
`≥ δ N / (q L)` on which the stride-`q` dilated, translated pullback `m ↦ T.eval (ℓ (b + q m))` has
bias `≥ δ / 3`, which is the input of the engine (`G1/Compose.lean`,
`exists_dilated_stride_symbol_factorization`).

* `residueSet`, `sum_Icc_eq_sum_residues`, `exists_residue_norm_ge`: the decomposition of
  `∑_{n ∈ [1, K]}` into the residue classes `n = q m + b` and the pigeonhole on the class;
* `class_sum_eq_interval`: on a class the indicator of `P` is constant times an indicator of an
  interval, so the class sum is a sum over an interval of `m`;
* `type_one_core`: the pigeonhole over `ℓ` and the length bounds, for a bounded `v : ℤ → ℂ`;
* `type_one_boxes`: the statement for a one-variable niltest `T` with `‖T‖ ≤ 1`.

The hypothesis `q * L ≤ N` holds in the application (`q ≤ e^p`, `L ≤ N^{2/3}`). No `gcd (ℓ, q)` case
split is needed: the class `b` of `n` mod `q` is pigeonholed directly.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Finset

/-- The `m` with `q m + b ∈ [1, K]`. -/
def residueSet (q : ℕ) (K b : ℤ) : Finset ℤ :=
  (Finset.Icc (0 : ℤ) K).filter fun m => 1 ≤ (q : ℤ) * m + b ∧ (q : ℤ) * m + b ≤ K

/-- Membership in `residueSet` for a residue `0 ≤ b < q`. -/
theorem mem_residueSet {q : ℕ} (hq : 1 ≤ q) {K b : ℤ} (hb0 : 0 ≤ b) (hbq : b < q) {m : ℤ} :
    m ∈ residueSet q K b ↔ 1 ≤ (q : ℤ) * m + b ∧ (q : ℤ) * m + b ≤ K := by
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  rw [residueSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2⟩
    have hm0 : 0 ≤ m := by
      by_contra h
      have : m ≤ -1 := by omega
      nlinarith
    refine ⟨⟨hm0, ?_⟩, h1, h2⟩
    nlinarith

/-- `∑_{n ∈ [1, K]} G n = ∑_{b < q} ∑_{m} G (q m + b)`. -/
theorem sum_Icc_eq_sum_residues (G : ℤ → ℂ) {q : ℕ} (hq : 1 ≤ q) (K : ℤ) :
    ∑ n ∈ Finset.Icc (1 : ℤ) K, G n =
      ∑ b ∈ Finset.Ico (0 : ℤ) q, ∑ m ∈ residueSet q K b, G (q * m + b) := by
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hmap : ∀ n ∈ Finset.Icc (1 : ℤ) K, (fun n : ℤ => n % (q : ℤ)) n ∈ Finset.Ico (0 : ℤ) q := by
    intro n _
    rw [Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  refine (Finset.sum_fiberwise_of_maps_to hmap G).symm.trans ?_
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_Ico] at hb
  obtain ⟨hb0, hbq⟩ := hb
  refine Finset.sum_nbij' (fun n => n / q) (fun m => q * m + b) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnK⟩, hnb⟩ := hn
    have h := Int.emod_add_mul_ediv n q
    rw [hnb] at h
    rw [mem_residueSet hq hb0 hbq]
    constructor <;> nlinarith
  · intro m hm
    rw [mem_residueSet hq hb0 hbq] at hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨hm, ?_⟩
    rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hb0 hbq]
  · intro n hn
    rw [Finset.mem_filter] at hn
    have h := Int.emod_add_mul_ediv n q
    rw [hn.2] at h
    change (q : ℤ) * (n / q) + b = n
    linarith
  · intro m _
    rw [add_comm, Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt hb0 hbq, zero_add]
  · intro n hn
    rw [Finset.mem_filter] at hn
    have h := Int.emod_add_mul_ediv n q
    rw [hn.2] at h
    change G n = G ((q : ℤ) * (n / q) + b)
    congr 1
    linarith

/-- Pigeonhole on the residue class: some class carries at least `1 / q` of the norm of the sum. -/
theorem exists_residue_norm_ge (G : ℤ → ℂ) {q : ℕ} (hq : 1 ≤ q) (K : ℤ) :
    ∃ b ∈ Finset.Ico (0 : ℤ) q, ‖∑ n ∈ Finset.Icc (1 : ℤ) K, G n‖ / q ≤
      ‖∑ m ∈ residueSet q K b, G (q * m + b)‖ := by
  have hne : (Finset.Ico (0 : ℤ) q).Nonempty := ⟨0, by rw [Finset.mem_Ico]; omega⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard : ((Finset.Ico (0 : ℤ) q).card : ℝ) = q := by
    rw [Int.card_Ico]
    simp
  refine Finset.exists_le_of_sum_le (f := fun _ => ‖∑ n ∈ Finset.Icc (1 : ℤ) K, G n‖ / q)
    (g := fun b => ‖∑ m ∈ residueSet q K b, G (q * m + b)‖) hne ?_
  rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_div_cancel₀ _ hq0.ne',
    sum_Icc_eq_sum_residues G hq K]
  exact norm_sum_le _ _

/-- The indicator of the progression `{n ∈ [lo, hi] : n ≡ r (mod q)}`. -/
def progIndicator (q : ℕ) (r lo hi : ℤ) (n : ℤ) : ℂ :=
  if lo ≤ n ∧ n ≤ hi ∧ n ≡ r [ZMOD q] then 1 else 0

/-- On a residue class `n = q m + b` with a nonzero sum, the indicator of the progression
is the indicator of an interval of `m`, and the class sum is a sum over that interval. -/
theorem class_sum_eq_interval (v : ℤ → ℂ) {q : ℕ} (hq : 1 ≤ q) (r lo hi : ℤ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) {K b : ℤ} (hb0 : 0 ≤ b) (hbq : b < q)
    (hZ : ∑ m ∈ residueSet q K b, progIndicator q r lo hi ((ℓ : ℤ) * (q * m + b)) *
      v ((ℓ : ℤ) * (q * m + b)) ≠ 0) :
    ∃ u w : ℤ, u ≤ w ∧ 1 ≤ (q : ℤ) * u + b ∧ (q : ℤ) * w + b ≤ K ∧
      ∑ m ∈ residueSet q K b, progIndicator q r lo hi ((ℓ : ℤ) * (q * m + b)) *
        v ((ℓ : ℤ) * (q * m + b)) =
      ∑ m ∈ Finset.Icc u w, v ((ℓ : ℤ) * b + (ℓ : ℤ) * q * m) := by
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hℓ' : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
  have hmod : ∀ m : ℤ, (ℓ : ℤ) * (q * m + b) ≡ (ℓ : ℤ) * b [ZMOD q] := by
    intro m
    rw [Int.modEq_iff_dvd]
    exact ⟨-((ℓ : ℤ) * m), by ring⟩
  by_cases hc : (ℓ : ℤ) * b ≡ r [ZMOD q]
  swap
  · exfalso
    apply hZ
    refine Finset.sum_eq_zero fun m _ => ?_
    have : ¬ (ℓ : ℤ) * (q * m + b) ≡ r [ZMOD q] := fun h => hc ((hmod m).symm.trans h)
    simp [progIndicator, this]
  have hind : ∀ m : ℤ, progIndicator q r lo hi ((ℓ : ℤ) * (q * m + b)) =
      if lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi then 1 else 0 := by
    intro m
    have h1 : (ℓ : ℤ) * (q * m + b) ≡ r [ZMOD q] := (hmod m).trans hc
    simp only [progIndicator, h1, and_true]
  obtain ⟨M', hM'⟩ : ∃ M' : Finset ℤ, M' = (residueSet q K b).filter
    (fun m => lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi) := ⟨_, rfl⟩
  have hmem : ∀ m, m ∈ M' ↔ (1 ≤ (q : ℤ) * m + b ∧ (q : ℤ) * m + b ≤ K) ∧
      lo ≤ (ℓ : ℤ) * (q * m + b) ∧ (ℓ : ℤ) * (q * m + b) ≤ hi := by
    intro m
    rw [hM', Finset.mem_filter, mem_residueSet hq hb0 hbq]
  have hsum : ∑ m ∈ residueSet q K b, progIndicator q r lo hi ((ℓ : ℤ) * (q * m + b)) *
      v ((ℓ : ℤ) * (q * m + b)) = ∑ m ∈ M', v ((ℓ : ℤ) * (q * m + b)) := by
    rw [hM', Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hind]
    split_ifs <;> simp
  have hne : M'.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [hsum, h, Finset.sum_empty] at hZ
    exact hZ rfl
  have hu := (hmem _).mp (Finset.min'_mem M' hne)
  have hw := (hmem _).mp (Finset.max'_mem M' hne)
  have huw : M'.min' hne ≤ M'.max' hne := Finset.min'_le_max' M' hne
  have hIcc : M' = Finset.Icc (M'.min' hne) (M'.max' hne) := by
    ext m
    constructor
    · intro hm
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le M' m hm, Finset.le_max' M' m hm⟩
    · intro hm
      rw [Finset.mem_Icc] at hm
      rw [hmem]
      obtain ⟨⟨hu1, hu1'⟩, hu2, hu3⟩ := hu
      obtain ⟨⟨hw1, hw1'⟩, hw2, hw3⟩ := hw
      have e1 : (q : ℤ) * M'.min' hne ≤ q * m := mul_le_mul_of_nonneg_left hm.1 (by omega)
      have e2 : (q : ℤ) * m ≤ q * M'.max' hne := mul_le_mul_of_nonneg_left hm.2 (by omega)
      have e3 : (ℓ : ℤ) * (q * M'.min' hne + b) ≤ ℓ * (q * m + b) :=
        mul_le_mul_of_nonneg_left (by linarith) (by omega)
      have e4 : (ℓ : ℤ) * (q * m + b) ≤ ℓ * (q * M'.max' hne + b) :=
        mul_le_mul_of_nonneg_left (by linarith) (by omega)
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  refine ⟨M'.min' hne, M'.max' hne, huw, hu.1.1, hw.1.2, ?_⟩
  rw [hsum]
  conv_lhs => rw [hIcc]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  ring

/-- Sums over `[1, K] ⊆ ℕ` (cast to `ℤ`) and over `[1, K] ⊆ ℤ` agree. -/
theorem sum_Icc_natCast_eq_int {M : Type*} [AddCommMonoid M] (g : ℤ → M) (K : ℕ) :
    ∑ n ∈ Icc 1 K, g (n : ℤ) = ∑ n ∈ Finset.Icc (1 : ℤ) K, g n := by
  refine Finset.sum_nbij' (fun n => (n : ℤ)) (fun z => z.toNat) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro z hz
    simp only [Finset.mem_Icc] at hz ⊢
    omega
  · intro n _
    simp
  · intro z hz
    simp only [Finset.mem_Icc] at hz
    omega
  · intro n _
    rfl

/-- **The type I step, the combinatorial core.**  For a function `v` bounded by one, the sums
`∑_{n ≤ ⌊N'/ℓ⌋} 1_P (ℓ n) v (ℓ n)` of norm `≥ δ N / L` for `≥ δ L` integers `ℓ ∈ (L/2, L]` give a
residue class `b` mod `q` and `≥ δ L / q` of the `ℓ` with a box `[o, o + len)`, `len ≥ δ N / (q L)`,
on which `‖∑_m v (ℓ (b + q m))‖ ≥ (δ / 3) len` (needs `q L ≤ N`). -/
theorem type_one_core (v : ℤ → ℂ) (hv : ∀ n, ‖v n‖ ≤ 1) {q : ℕ} (hq : 1 ≤ q) (r lo hi : ℤ)
    {N N' L : ℕ} (hN : 1 ≤ N) (hN' : N' ≤ N) (hL : 1 ≤ L) (hqL : q * L ≤ N)
    {δ : ℝ} (hδ : 0 < δ) {Λ : Finset ℕ}
    (hΛ : ∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) (hcard : δ * L ≤ Λ.card)
    (hsum : ∀ ℓ ∈ Λ, δ * ((N : ℝ) / L) ≤ ‖∑ n ∈ Finset.Icc 1 ⌊(N' : ℝ) / ℓ⌋₊,
      progIndicator q r lo hi ((ℓ : ℤ) * n) * v ((ℓ : ℤ) * n)‖) :
    ∃ b : ℤ, ∃ Λ' ⊆ Λ, δ * L / q ≤ Λ'.card ∧ ∀ ℓ ∈ Λ', ∃ (o : ℤ) (len : ℕ),
      δ * ((N : ℝ) / (q * L)) ≤ len ∧
      δ / 3 * len ≤ ‖∑ m ∈ Finset.Ico o (o + len), v ((ℓ : ℤ) * b + (ℓ : ℤ) * q * m)‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓ1 : ∀ ℓ ∈ Λ, 1 ≤ ℓ := by
    intro ℓ hℓ
    have := (hΛ ℓ hℓ).1
    have h2 : (0 : ℝ) < ℓ := by linarith [show (0 : ℝ) < (L : ℝ) / 2 by positivity]
    exact_mod_cast h2
  -- the residue class of each `ℓ`
  have hex : ∀ ℓ : ℕ, ∃ b : ℤ, ℓ ∈ Λ → (b ∈ Finset.Ico (0 : ℤ) q ∧
      ‖∑ n ∈ Finset.Icc (1 : ℤ) (⌊(N' : ℝ) / ℓ⌋₊ : ℕ),
          progIndicator q r lo hi ((ℓ : ℤ) * n) * v ((ℓ : ℤ) * n)‖ / q ≤
        ‖∑ m ∈ residueSet q ((⌊(N' : ℝ) / ℓ⌋₊ : ℕ) : ℤ) b,
          progIndicator q r lo hi ((ℓ : ℤ) * (q * m + b)) * v ((ℓ : ℤ) * (q * m + b))‖) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ Λ
    · obtain ⟨b, hb, h⟩ := exists_residue_norm_ge
        (fun n : ℤ => progIndicator q r lo hi ((ℓ : ℤ) * n) * v ((ℓ : ℤ) * n)) hq
        ((⌊(N' : ℝ) / ℓ⌋₊ : ℕ) : ℤ)
      exact ⟨b, fun _ => ⟨hb, h⟩⟩
    · exact ⟨0, fun h => absurd h hℓ⟩
  choose β hβ using hex
  have hmaps : ∀ ℓ ∈ Λ, β ℓ ∈ Finset.Ico (0 : ℤ) q := fun ℓ hℓ => (hβ ℓ hℓ).1
  have hne : (Finset.Ico (0 : ℤ) q).Nonempty := ⟨0, by rw [Finset.mem_Ico]; omega⟩
  have hcardIco : ((Finset.Ico (0 : ℤ) q).card : ℝ) = q := by
    rw [Int.card_Ico]
    simp
  obtain ⟨b₀, hb₀, hfib⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (b := (Λ.card : ℝ) / q) hmaps hne (by
      rw [nsmul_eq_mul, hcardIco, mul_div_cancel₀ _ hq0.ne'])
  refine ⟨b₀, Λ.filter (fun ℓ => β ℓ = b₀), Finset.filter_subset _ _, ?_, ?_⟩
  · refine le_trans ?_ hfib
    exact div_le_div_of_nonneg_right hcard hq0.le
  · intro ℓ hℓ'
    rw [Finset.mem_filter] at hℓ'
    obtain ⟨hℓ, hβℓ⟩ := hℓ'
    obtain ⟨hbmem, hbound⟩ := hβ ℓ hℓ
    rw [hβℓ] at hbmem hbound
    rw [Finset.mem_Ico] at hbmem
    obtain ⟨hb0, hbq⟩ := hbmem
    have hℓ1' := hℓ1 ℓ hℓ
    have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1'
    generalize hKdef : ⌊(N' : ℝ) / ℓ⌋₊ = K at hbound
    have hKle : (K : ℝ) ≤ (N : ℝ) / ℓ := by
      rw [← hKdef]
      calc ((⌊(N' : ℝ) / ℓ⌋₊ : ℕ) : ℝ) ≤ (N' : ℝ) / ℓ := Nat.floor_le (by positivity)
        _ ≤ N / ℓ := div_le_div_of_nonneg_right (by exact_mod_cast hN') hℓ0.le
    have hS := hsum ℓ hℓ
    rw [hKdef] at hS
    have hSz : δ * ((N : ℝ) / L) ≤ ‖∑ n ∈ Finset.Icc (1 : ℤ) (K : ℤ),
        progIndicator q r lo hi ((ℓ : ℤ) * n) * v ((ℓ : ℤ) * n)‖ := by
      have := sum_Icc_natCast_eq_int
        (fun z : ℤ => progIndicator q r lo hi ((ℓ : ℤ) * z) * v ((ℓ : ℤ) * z)) K
      rw [← this]
      exact hS
    have hZpos : δ * ((N : ℝ) / (q * L)) ≤ ‖∑ m ∈ residueSet q (K : ℤ) b₀,
        progIndicator q r lo hi ((ℓ : ℤ) * (q * m + b₀)) * v ((ℓ : ℤ) * (q * m + b₀))‖ := by
      calc δ * ((N : ℝ) / (q * L)) = (δ * ((N : ℝ) / L)) / q := by field_simp
        _ ≤ _ / q := div_le_div_of_nonneg_right hSz hq0.le
        _ ≤ _ := hbound
    have hδY : 0 < δ * ((N : ℝ) / (q * L)) := by positivity
    have hZne : ∑ m ∈ residueSet q (K : ℤ) b₀,
        progIndicator q r lo hi ((ℓ : ℤ) * (q * m + b₀)) * v ((ℓ : ℤ) * (q * m + b₀)) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hZpos
      linarith
    obtain ⟨u, w, huw, hu1, hw1, hZeq⟩ := class_sum_eq_interval v hq r lo hi hℓ1' hb0 hbq hZne
    have hlen : (((w + 1 - u).toNat : ℕ) : ℤ) = w + 1 - u := Int.toNat_of_nonneg (by omega)
    have hIco : Finset.Ico u (u + (((w + 1 - u).toNat : ℕ) : ℤ)) = Finset.Icc u w := by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    refine ⟨u, (w + 1 - u).toNat, ?_⟩
    rw [hIco, ← hZeq]
    have hZle : ‖∑ m ∈ residueSet q (K : ℤ) b₀,
        progIndicator q r lo hi ((ℓ : ℤ) * (q * m + b₀)) * v ((ℓ : ℤ) * (q * m + b₀))‖ ≤
        (((w + 1 - u).toNat : ℕ) : ℝ) := by
      rw [hZeq]
      calc ‖∑ m ∈ Finset.Icc u w, v ((ℓ : ℤ) * b₀ + (ℓ : ℤ) * q * m)‖
          ≤ ∑ m ∈ Finset.Icc u w, (1 : ℝ) := norm_sum_le_of_le _ (fun m _ => hv _)
        _ = (((w + 1 - u).toNat : ℕ) : ℝ) := by
            rw [Finset.sum_const, Int.card_Icc]
            simp
    refine ⟨hZpos.trans hZle, ?_⟩
    -- the upper bound on the length
    have hlenZ : (q : ℤ) * (((w + 1 - u).toNat : ℕ) : ℤ) ≤ (K : ℤ) - 1 + q := by
      rw [hlen]
      linarith only [hu1, hw1]
    have hlenR : (q : ℝ) * (((w + 1 - u).toNat : ℕ) : ℝ) ≤ (K : ℝ) - 1 + q := by
      exact_mod_cast hlenZ
    have hL2 : (L : ℝ) ≤ 2 * ℓ := by linarith [(hΛ ℓ hℓ).1]
    have hNℓ : (N : ℝ) / ℓ ≤ 2 * N / L := by
      rw [div_le_div_iff₀ hℓ0 hL0]
      linarith only [mul_le_mul_of_nonneg_left hL2 hN0.le]
    have hY1 : 1 ≤ (N : ℝ) / (q * L) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact_mod_cast hqL
    have hlenY : (((w + 1 - u).toNat : ℕ) : ℝ) ≤ 3 * ((N : ℝ) / (q * L)) := by
      have h1 : (((w + 1 - u).toNat : ℕ) : ℝ) * q ≤ 2 * N / L + q := by linarith
      have h2 : (((w + 1 - u).toNat : ℕ) : ℝ) ≤ (2 * N / L + q) / q :=
        (le_div_iff₀ hq0).mpr h1
      have h3 : (2 * (N : ℝ) / L + q) / q = 2 * ((N : ℝ) / (q * L)) + 1 := by
        field_simp
      linarith
    calc δ / 3 * (((w + 1 - u).toNat : ℕ) : ℝ) ≤ δ / 3 * (3 * ((N : ℝ) / (q * L))) :=
          mul_le_mul_of_nonneg_left hlenY (by positivity)
      _ = δ * ((N : ℝ) / (q * L)) := by ring
      _ ≤ _ := hZpos

section Niltest

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

/-- The mean over the one-variable box `[o, o + len)`. -/
theorem expect_translatedIntegerBox_unit (o : ℤ) (len : ℕ) (hlen : 0 < len)
    (g : (Unit → ℤ) → ℂ) :
    𝔼 x ∈ translatedIntegerBox (fun _ : Unit => o) (fun _ : Unit => len), g x =
      (len : ℂ)⁻¹ * ∑ m ∈ Finset.Ico o (o + len), g (fun _ => m) := by
  have hbox : translatedIntegerBox (fun _ : Unit => o) (fun _ : Unit => len) =
      (Finset.Ico o (o + len)).image (fun m : ℤ => fun _ : Unit => m) := by
    ext x
    rw [mem_translatedIntegerBox, Finset.mem_image]
    constructor
    · intro h
      refine ⟨x (), ?_, ?_⟩
      · rw [Finset.mem_Ico]
        exact h ()
      · funext i
        cases i
        rfl
    · rintro ⟨m, hm, rfl⟩ i
      rw [Finset.mem_Ico] at hm
      exact hm
  have hinj : Function.Injective (fun m : ℤ => fun _ : Unit => m) := fun a b h =>
    congrFun h ()
  rw [hbox, Finset.expect_eq_sum_div_card, Finset.sum_image (fun a _ b _ h => hinj h),
    Finset.card_image_of_injective _ hinj, Int.card_Ico]
  have : (o + (len : ℤ) - o).toNat = len := by omega
  rw [this, div_eq_inv_mul]

/-- The sequence `φ = 1_P · star (T.eval)` of the type I step, `P = {n ∈ [lo, hi] : n ≡ r (q)}`. -/
def typeISequence (T : D.Niltest (fun _ : Unit => 1)) (q : ℕ) (r lo hi : ℤ) (n : ℤ) : ℂ :=
  progIndicator q r lo hi n * star (T.eval fun _ => n)

/-- **The type I step: dilated boxes** (Leng23 Prop 5.2, `Final_Version.tex` L1130-1138). Let `T` be
a one-variable niltest with `‖T‖ ≤ 1`, `P = {n ∈ [lo, hi] : n ≡ r (q)}` and
`φ = 1_P · star (T.eval)`. If `≥ δ L` integers `ℓ ∈ (L/2, L]` have
`‖∑_{n ≤ ⌊N'/ℓ⌋} φ (ℓ n)‖ ≥ δ N / L` (the type I output of the Vaughan decomposition) and `q L ≤ N`,
then there are a class `b` mod `q` and `≥ δ L / q` of the `ℓ`, each with a box `[o, o + len)` of
length `≥ δ N / (q L)` on which the pullback `m ↦ T.eval (ℓ b + ℓ q m)` has bias `≥ δ / 3`. -/
theorem type_one_boxes (T : D.Niltest (fun _ : Unit => 1)) (hT : (T.normBound : ℝ) ≤ 1)
    {q : ℕ} (hq : 1 ≤ q) (r lo hi : ℤ) {N N' L : ℕ} (hN : 1 ≤ N) (hN' : N' ≤ N) (hL : 1 ≤ L)
    (hqL : q * L ≤ N) {δ : ℝ} (hδ : 0 < δ) {Λ : Finset ℕ}
    (hΛ : ∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) (hcard : δ * L ≤ Λ.card)
    (hsum : ∀ ℓ ∈ Λ, δ * ((N : ℝ) / L) ≤ ‖∑ n ∈ Finset.Icc 1 ⌊(N' : ℝ) / ℓ⌋₊,
      typeISequence T q r lo hi ((ℓ : ℤ) * n)‖) :
    ∃ b : ℤ, ∃ Λ' ⊆ Λ, δ * L / q ≤ Λ'.card ∧ ∀ ℓ ∈ Λ', ∃ (o : ℤ) (len : ℕ),
      δ * ((N : ℝ) / (q * L)) ≤ len ∧ δ / 3 ≤ ‖𝔼 m ∈ translatedIntegerBox
        (fun _ : Unit => o) (fun _ : Unit => len),
        (T.affinePullback (fun (_ : Unit) (_ : Unit) => (ℓ : ℤ) * (q : ℤ))
          (fun _ : Unit => (ℓ : ℤ) * b)).eval m‖ := by
  have hv : ∀ n : ℤ, ‖star (T.eval fun _ : Unit => n)‖ ≤ 1 := fun n => by
    rw [norm_star]
    exact (T.norm_eval_le _).trans hT
  obtain ⟨b, Λ', hsub, hcard', hbox⟩ := type_one_core (fun n => star (T.eval fun _ : Unit => n)) hv
    hq r lo hi hN hN' hL hqL hδ hΛ hcard hsum
  refine ⟨b, Λ', hsub, hcard', fun ℓ hℓ => ?_⟩
  obtain ⟨o, len, hlen, hmean⟩ := hbox ℓ hℓ
  refine ⟨o, len, hlen, ?_⟩
  have hY : 0 < δ * ((N : ℝ) / (q * L)) := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    have : (0 : ℝ) < L := by exact_mod_cast hL
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hlen0 : 0 < len := by
    have : (0 : ℝ) < len := lt_of_lt_of_le hY hlen
    exact_mod_cast this
  rw [expect_translatedIntegerBox_unit o len hlen0, norm_mul, norm_inv, Complex.norm_natCast]
  have hsumeq : ‖∑ m ∈ Finset.Ico o (o + len),
      (T.affinePullback (fun (_ : Unit) (_ : Unit) => (ℓ : ℤ) * (q : ℤ))
        (fun _ : Unit => (ℓ : ℤ) * b)).eval (fun _ => m)‖ =
      ‖∑ m ∈ Finset.Ico o (o + len), star (T.eval fun _ : Unit => (ℓ : ℤ) * b +
        (ℓ : ℤ) * q * m)‖ := by
    rw [← norm_star, star_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [affinePullback_unit_eval]
  rw [hsumeq]
  have hlenR : (0 : ℝ) < len := by exact_mod_cast hlen0
  rw [inv_mul_eq_div, le_div_iff₀ hlenR]
  linarith

end Niltest

end PrimeCarleson.Proof.Fplus31
