module

public import PrimeCarleson.Proof.Fplus31.Vinogradov.Torus
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Window counting for sequences close to integers

Vinogradov-type estimate used by the extrapolation step of the iteration of `C2/CMain.lean` (proof
of [F+] Proposition 3.1) (Leng's `l:vinogradov`, arXiv:2312.10772v5 TeX
L1471). The counting step behind the linear Vinogradov lemma: if `‖θ j + c‖_{ℝ/ℤ} ≤ ε` for all
integers `j` in a finite set `S` lying in a real interval of length `J`, then `S` has at most
`(2 ε / |θ| + 1)(|θ| J + 2 ε + 1)` elements (`card_le_of_norm_le`, `card_le_of_norm_le_abs`). The
proof maps `j` to the nearest integer of `θ j + c`: the fibres lie in windows of length `2 ε / |θ|`
and the image in a window of length `|θ| J + 2 ε`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The number of integers in `[u, v]` is at most `v - u + 1` (when `u ≤ v + 1`). -/
theorem card_Icc_int_le (u v : ℝ) (huv : u ≤ v + 1) :
    ((Finset.Icc ⌈u⌉ ⌊v⌋).card : ℝ) ≤ v - u + 1 := by
  rw [Int.card_Icc]
  by_cases h : 0 ≤ ⌊v⌋ + 1 - ⌈u⌉
  · have h1 : (((⌊v⌋ + 1 - ⌈u⌉).toNat : ℤ) : ℝ) = ((⌊v⌋ + 1 - ⌈u⌉ : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg h]
    have h2 : (((⌊v⌋ + 1 - ⌈u⌉).toNat : ℕ) : ℝ) = ((⌊v⌋ + 1 - ⌈u⌉ : ℤ) : ℝ) := by
      exact_mod_cast h1
    rw [h2]
    push_cast
    have := Int.floor_le v
    have := Int.le_ceil u
    linarith
  · have h1 : (⌊v⌋ + 1 - ⌈u⌉).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h1]
    push_cast
    linarith

/-- A fibre of `j ↦ round (θ j + c)` over a set where `θ j + c` is within `ε` of its nearest
integer has at most `⌊2 ε / θ⌋ + 1` elements. -/
theorem card_fiber_le {θ c ε : ℝ} (hθ : 0 < θ) (hε : 0 ≤ ε) (S : Finset ℤ) (m : ℤ)
    (h : ∀ j ∈ S, |θ * (j : ℝ) + c - (round (θ * (j : ℝ) + c) : ℤ)| ≤ ε) :
    (S.filter (fun j : ℤ => round (θ * (j : ℝ) + c) = m)).card ≤ ⌊2 * ε / θ⌋₊ + 1 := by
  set F := S.filter (fun j : ℤ => round (θ * (j : ℝ) + c) = m) with hF
  rcases F.eq_empty_or_nonempty with he | hne
  · rw [he]
    simp
  · set j₀ := F.min' hne with hj₀
    have hj₀mem : j₀ ∈ F := F.min'_mem hne
    have hsub : F ⊆ Finset.Icc j₀ (j₀ + (⌊2 * ε / θ⌋₊ : ℤ)) := by
      intro j hj
      rw [Finset.mem_Icc]
      refine ⟨F.min'_le j hj, ?_⟩
      have hj' := hj
      have hj₀' := hj₀mem
      rw [hF, Finset.mem_filter] at hj' hj₀'
      have h1 := h j hj'.1
      have h2 := h j₀ hj₀'.1
      rw [hj'.2] at h1
      rw [hj₀'.2] at h2
      have hlt : (j : ℝ) - j₀ ≤ 2 * ε / θ := by
        rw [le_div_iff₀ hθ]
        have := abs_le.mp h1
        have := abs_le.mp h2
        nlinarith
      have h4 : j - j₀ ≤ ⌊2 * ε / θ⌋ := Int.le_floor.mpr (by push_cast; exact hlt)
      have h5 : (⌊2 * ε / θ⌋₊ : ℤ) = ⌊2 * ε / θ⌋ := Int.natCast_floor_eq_floor (by positivity)
      omega
    have h3 := Finset.card_le_card hsub
    rw [Int.card_Icc] at h3
    have h6 : (j₀ + (⌊2 * ε / θ⌋₊ : ℤ) + 1 - j₀).toNat = ⌊2 * ε / θ⌋₊ + 1 := by omega
    rwa [h6] at h3

/-- **Window counting.**  If `θ > 0` and `θ j + c` is within `ε` (modulo `1`) of an integer for the
integers `j` of a set `S` lying in a real interval of length `J`, then `S` has at most
`(2 ε / θ + 1)(θ J + 2 ε + 1)` elements. -/
theorem card_le_of_norm_le {θ c ε a J : ℝ} (hθ : 0 < θ) (hε : 0 ≤ ε) (hJ : 0 ≤ J)
    (S : Finset ℤ) (hS : ∀ j ∈ S, a ≤ (j : ℝ) ∧ (j : ℝ) ≤ a + J)
    (h : ∀ j ∈ S, ‖((θ * (j : ℝ) + c : ℝ) : UnitAddCircle)‖ ≤ ε) :
    (S.card : ℝ) ≤ (2 * ε / θ + 1) * (θ * J + 2 * ε + 1) := by
  set f : ℤ → ℤ := fun j => round (θ * (j : ℝ) + c) with hf
  have hf' : ∀ j ∈ S, |θ * (j : ℝ) + c - (f j : ℝ)| ≤ ε := by
    intro j hj
    have := h j hj
    rwa [norm_coe_eq_abs_sub_round] at this
  have hfib : ∀ b ∈ S.image f, (S.filter (fun j => f j = b)).card ≤ ⌊2 * ε / θ⌋₊ + 1 :=
    fun b _ => card_fiber_le hθ hε S b hf'
  have h1 := Finset.card_le_mul_card_image (f := f) S _ hfib
  have himg : ((S.image f).card : ℝ) ≤ θ * J + 2 * ε + 1 := by
    have hsub : S.image f ⊆ Finset.Icc ⌈θ * a + c - ε⌉ ⌊θ * (a + J) + c + ε⌋ := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      rw [Finset.mem_Icc]
      have := abs_le.mp (hf' j hj)
      obtain ⟨hj1, hj2⟩ := hS j hj
      constructor
      · apply Int.ceil_le.mpr
        nlinarith
      · apply Int.le_floor.mpr
        nlinarith
    have h2 := Finset.card_le_card hsub
    have h3 := card_Icc_int_le (θ * a + c - ε) (θ * (a + J) + c + ε) (by nlinarith)
    have h4 : ((S.image f).card : ℝ)
        ≤ ((Finset.Icc ⌈θ * a + c - ε⌉ ⌊θ * (a + J) + c + ε⌋).card : ℝ) := by
      exact_mod_cast h2
    nlinarith
  have h5 : (S.card : ℝ) ≤ ((⌊2 * ε / θ⌋₊ + 1 : ℕ) : ℝ) * ((S.image f).card : ℝ) := by
    exact_mod_cast h1
  have h6 : ((⌊2 * ε / θ⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * ε / θ + 1 := by
    push_cast
    have := Nat.floor_le (a := 2 * ε / θ) (by positivity)
    linarith
  calc (S.card : ℝ) ≤ _ := h5
    _ ≤ (2 * ε / θ + 1) * (θ * J + 2 * ε + 1) := by
      apply mul_le_mul h6 himg (by positivity) (by positivity)

/-- The window count for a parameter `θ ≠ 0` of either sign: at most
`(2 ε / |θ| + 1)(|θ| J + 2 ε + 1)` elements. -/
theorem card_le_of_norm_le_abs {θ c ε a J : ℝ} (hθ : θ ≠ 0) (hε : 0 ≤ ε) (hJ : 0 ≤ J)
    (S : Finset ℤ) (hS : ∀ j ∈ S, a ≤ (j : ℝ) ∧ (j : ℝ) ≤ a + J)
    (h : ∀ j ∈ S, ‖((θ * (j : ℝ) + c : ℝ) : UnitAddCircle)‖ ≤ ε) :
    (S.card : ℝ) ≤ (2 * ε / |θ| + 1) * (|θ| * J + 2 * ε + 1) := by
  rcases hθ.lt_or_gt with hneg | hpos
  · have h' : ∀ j ∈ S, ‖(((-θ) * (j : ℝ) + (-c) : ℝ) : UnitAddCircle)‖ ≤ ε := by
      intro j hj
      have := h j hj
      rw [← norm_coe_neg] at this
      convert this using 3
      ring
    have := card_le_of_norm_le (neg_pos.mpr hneg) hε hJ S hS h'
    rwa [abs_of_neg hneg]
  · rw [abs_of_pos hpos]
    exact card_le_of_norm_le hpos hε hJ S hS h

end PrimeCarleson.Proof.Fplus31
