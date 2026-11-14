module

public import PrimeCarleson.Proof.Fplus31.C2.IterationAP

/-!
# The iteration, the cells of a progression

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). A
progression `P' = {n ∈ [lo, lo + K B - 1] : n ≡ r (q)}` is cut into the `K` blocks
`[lo + a B, lo + (a+1) B)` of equal length `B`; inside the block `a` the residue classes modulo
`m a`, a multiple of `q` (the stride `q` times the period of the model of the block), give
cells `apInt (m a) ρ (lo + a B) (lo + a B + B - 1)`, which are again progressions of the same shape.
The cell of a point `n` is `cellOf lo B m n = (a, n mod m a)`; `fibre_eq_apInt` identifies the fibre
of the cell map with the progression, and `card_apInt_block_ge` bounds its size from below.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Finset
open scoped BigOperators

/-- The index of the block of length `B` starting at `lo` that contains `n`. -/
def blkIdx (lo : ℤ) (B : ℕ) (n : ℤ) : ℕ := ((n - lo) / (B : ℤ)).toNat

/-- The cell of `n`: its block and its residue modulo the modulus `m a` of that block. -/
def cellOf (lo : ℤ) (B : ℕ) (m : ℕ → ℕ) (n : ℤ) : ℕ × ℤ :=
  (blkIdx lo B n, n % ((m (blkIdx lo B n) : ℕ) : ℤ))

/-- For `n ≥ lo`, the block index and offset: `n = lo + B a + s`, `0 ≤ s < B`. -/
theorem blkIdx_spec {lo : ℤ} {B : ℕ} (hB : 0 < B) {n : ℤ} (hn : lo ≤ n) :
    lo + (blkIdx lo B n : ℤ) * B ≤ n ∧ n < lo + (blkIdx lo B n : ℤ) * B + B := by
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have h0 : 0 ≤ (n - lo) / (B : ℤ) := Int.ediv_nonneg (by omega) hB'.le
  have hcast : ((blkIdx lo B n : ℕ) : ℤ) = (n - lo) / (B : ℤ) := by
    simp only [blkIdx]
    exact Int.toNat_of_nonneg h0
  rw [hcast]
  have e := Int.mul_ediv_add_emod (n - lo) (B : ℤ)
  have h1 := Int.emod_nonneg (n - lo) hB'.ne'
  have h2 := Int.emod_lt_of_pos (n - lo) hB'
  set t := (n - lo) / (B : ℤ)
  set s := (n - lo) % (B : ℤ)
  constructor <;> nlinarith

/-- A point is in the block `a` iff its block index is `a`. -/
theorem blkIdx_eq_iff {lo : ℤ} {B : ℕ} (hB : 0 < B) {n : ℤ} (hn : lo ≤ n) {a : ℕ} :
    blkIdx lo B n = a ↔ lo + (a : ℤ) * B ≤ n ∧ n < lo + (a : ℤ) * B + B := by
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  obtain ⟨h1, h2⟩ := blkIdx_spec hB hn
  constructor
  · rintro rfl
    exact ⟨h1, h2⟩
  · rintro ⟨h3, h4⟩
    have : (blkIdx lo B n : ℤ) = a := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (blkIdx lo B n : ℤ) + 1 ≤ a := by omega
        nlinarith
      · have : (a : ℤ) + 1 ≤ blkIdx lo B n := by omega
        nlinarith
    exact_mod_cast this

/-- A point of `P' = apInt q r lo (lo + K B - 1)` lies in a block `a < K`. -/
theorem blkIdx_lt {q : ℕ} {r lo : ℤ} {B K : ℕ} (hB : 0 < B) {n : ℤ}
    (hn : n ∈ apInt q r lo (lo + K * B - 1)) : blkIdx lo B n < K := by
  obtain ⟨h1, h2, -⟩ := mem_apInt.mp hn
  obtain ⟨h3, -⟩ := blkIdx_spec hB h1
  by_contra hK
  push Not at hK
  have : (K : ℤ) ≤ blkIdx lo B n := by exact_mod_cast hK
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  nlinarith

/-- **The fibre of the cell map is a progression.**  For `P' = apInt q r lo (lo + K B - 1)`, a
family of moduli `m a` which are positive multiples of `q`, and `n₀ ∈ P'` with cell `(a, ρ)`, the
points of `P'` of the same cell form the progression of modulus `m a` and residue `ρ` in the
block `a`. -/
theorem fibre_eq_apInt {q : ℕ} {r lo : ℤ} {B K : ℕ} (hB : 0 < B) {m : ℕ → ℕ}
    (hm : ∀ a, 0 < m a ∧ q ∣ m a) {n₀ : ℤ} (hn₀ : n₀ ∈ apInt q r lo (lo + K * B - 1)) :
    (apInt q r lo (lo + K * B - 1)).filter (fun n => cellOf lo B m n = cellOf lo B m n₀) =
      apInt (m (blkIdx lo B n₀)) (n₀ % (m (blkIdx lo B n₀) : ℤ))
        (lo + (blkIdx lo B n₀ : ℤ) * B) (lo + (blkIdx lo B n₀ : ℤ) * B + B - 1) := by
  set a := blkIdx lo B n₀ with ha
  have haK : a < K := blkIdx_lt hB hn₀
  obtain ⟨hn₀1, hn₀2, hn₀r⟩ := mem_apInt.mp hn₀
  have hma : (0 : ℤ) < (m a : ℤ) := by exact_mod_cast (hm a).1
  ext n
  simp only [Finset.mem_filter, mem_apInt, cellOf, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hn1, hn2, hnr⟩, hba, hmod⟩
    have hba' : blkIdx lo B n = a := hba
    rw [hba'] at hmod
    obtain ⟨h1, h2⟩ := (blkIdx_eq_iff hB hn1).mp hba'
    refine ⟨h1, by omega, ?_⟩
    unfold Int.ModEq
    rw [Int.emod_emod_of_dvd _ dvd_rfl]
    exact hmod
  · rintro ⟨h1, h2, hmod⟩
    have hlo : lo ≤ n := by
      have : (0 : ℤ) ≤ (a : ℤ) * B := by positivity
      linarith
    have hKa : ((a : ℤ) + 1) * B ≤ K * B := by
      have : (a : ℤ) + 1 ≤ K := by exact_mod_cast haK
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hba : blkIdx lo B n = a := (blkIdx_eq_iff hB hlo).mpr ⟨h1, by omega⟩
    refine ⟨⟨hlo, by nlinarith, ?_⟩, hba, ?_⟩
    · have hq : (q : ℤ) ∣ (m a : ℤ) := by exact_mod_cast (hm a).2
      have h3 : n ≡ n₀ [ZMOD (m a : ℤ)] := by
        refine hmod.trans ?_
        exact Int.mod_modEq n₀ _
      exact (Int.ModEq.of_dvd hq h3).trans hn₀r
    · rw [hba]
      unfold Int.ModEq at hmod
      rw [Int.emod_emod_of_dvd _ dvd_rfl] at hmod
      exact hmod

/-- **A block of length `B` contains at least `B / m` points of each residue class modulo `m`.** -/
theorem card_apInt_block_ge {m : ℕ} (hm : 0 < m) (ρ u : ℤ) (B : ℕ) :
    B / m ≤ (apInt m ρ u (u + B - 1)).card := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set n₁ : ℤ := u + (ρ - u) % (m : ℤ) with hn₁
  have h0 : 0 ≤ (ρ - u) % (m : ℤ) := Int.emod_nonneg _ hm'.ne'
  have h1 : (ρ - u) % (m : ℤ) < m := Int.emod_lt_of_pos _ hm'
  have hcm : (B / m) * m ≤ B := Nat.div_mul_le_self B m
  have hmaps : ∀ j ∈ Finset.range (B / m), n₁ + (j : ℤ) * m ∈ apInt m ρ u (u + B - 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    refine mem_apInt.mpr ⟨by nlinarith, ?_, ?_⟩
    · have hj1 : (j : ℤ) + 1 ≤ ((B / m : ℕ) : ℤ) := by exact_mod_cast hj
      have hcm' : (((B / m : ℕ) : ℤ)) * m ≤ B := by exact_mod_cast hcm
      nlinarith
    · have : n₁ ≡ ρ [ZMOD (m : ℤ)] := by
        have hmm := Int.mod_modEq (ρ - u) (m : ℤ)
        have : u + (ρ - u) % (m : ℤ) ≡ u + (ρ - u) [ZMOD (m : ℤ)] := Int.ModEq.add_left u hmm
        simpa using this
      refine (this.add_right _).trans ?_
      simp [Int.modEq_iff_dvd]
  calc B / m = (Finset.range (B / m)).card := (Finset.card_range _).symm
    _ ≤ (apInt m ρ u (u + B - 1)).card := by
      refine Finset.card_le_card_of_injOn (fun j : ℕ => n₁ + (j : ℤ) * m) hmaps ?_
      intro i _ j _ hij
      have : (i : ℤ) * m = j * m := by simpa using hij
      have := mul_right_cancel₀ hm'.ne' this
      exact_mod_cast this

end PrimeCarleson.Proof.Fplus31
