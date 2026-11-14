module

public import PrimeCarleson.Proof.Fplus31.Vinogradov.Linear

/-!
# Differencing: dense sets of shifts with dense intersections

Vinogradov-type estimate used by the extrapolation step of the iteration of `C2/CMain.lean` (proof
of [F+] Proposition 3.1), degree two (differencing `P(ℓ+h) - P(ℓ)` and pigeonholing over `h` in a
dense set). Combinatorial inputs for the quadratic Vinogradov lemma:

* `exists_fiber_ge`: pigeonhole with a real-valued bound on the fibre size;
* `sum_card_shift`: `∑_h |Λ ∩ (Λ - h)| = |Λ|²` when the index set contains all differences;
* `exists_dense_shifts`: there is a set `H` of at least `|Λ| / 2` shifts `h` such that
  `|Λ ∩ (Λ - h)| ≥ |Λ|² / (2 |D|)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- Pigeonhole with a real bound: some fibre of `f : s → t` has at least `|s| / |t|` elements. -/
theorem exists_fiber_ge {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ) (f : ι → κ)
    (hf : ∀ i ∈ s, f i ∈ t) (ht : t.Nonempty) :
    ∃ y ∈ t, (s.card : ℝ) / t.card ≤ (s.filter (fun i => f i = y)).card := by
  have hpos : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  refine Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to (M := ℝ) hf ht ?_
  rw [nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']

/-- Double counting: when `D` contains all differences of elements of `Λ`, the sizes of the
sets `{ℓ ∈ Λ : ℓ + h ∈ Λ}` for `h ∈ D` add up to `|Λ|²`. -/
theorem sum_card_shift (Λ D : Finset ℤ) (hD : ∀ ℓ ∈ Λ, ∀ ℓ' ∈ Λ, ℓ' - ℓ ∈ D) :
    ∑ h ∈ D, (Λ.filter (fun ℓ => ℓ + h ∈ Λ)).card = Λ.card ^ 2 := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ ℓ ∈ Λ, ∑ h ∈ D, (if ℓ + h ∈ Λ then 1 else 0) = Λ.card := by
    intro ℓ hℓ
    rw [← Finset.card_filter]
    have : D.filter (fun h => ℓ + h ∈ Λ) = Λ.image (fun ℓ' => ℓ' - ℓ) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨_, hh⟩
        exact ⟨ℓ + h, hh, by ring⟩
      · rintro ⟨ℓ', hℓ', rfl⟩
        exact ⟨hD ℓ hℓ ℓ' hℓ', by simpa using hℓ'⟩
    rw [this, Finset.card_image_of_injective _ (sub_left_injective)]
  rw [Finset.sum_congr rfl key]
  simp [sq]

/-- **Dense set of shifts.**  If `D` contains all differences of elements of a nonempty `Λ`,
there is `H ⊆ D` with `|H| ≥ |Λ| / 2` such that
`|{ℓ ∈ Λ : ℓ + h ∈ Λ}| ≥ |Λ|² / (2 |D|)` for `h ∈ H`. -/
theorem exists_dense_shifts (Λ D : Finset ℤ) (hD : ∀ ℓ ∈ Λ, ∀ ℓ' ∈ Λ, ℓ' - ℓ ∈ D)
    (hΛ : Λ.Nonempty) :
    ∃ H ⊆ D, (Λ.card : ℝ) / 2 ≤ H.card ∧
      ∀ h ∈ H, (Λ.card : ℝ) ^ 2 / (2 * D.card) ≤ (Λ.filter (fun ℓ => ℓ + h ∈ Λ)).card := by
  obtain ⟨ℓ₀, hℓ₀⟩ := hΛ
  have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨0, by simpa using hD ℓ₀ hℓ₀ ℓ₀ hℓ₀⟩
  have hDpos' : (0 : ℝ) < D.card := by exact_mod_cast hDpos
  have hnpos : (0 : ℝ) < Λ.card := by exact_mod_cast Finset.card_pos.mpr ⟨ℓ₀, hℓ₀⟩
  have hsum : ∑ h ∈ D, ((Λ.filter (fun ℓ => ℓ + h ∈ Λ)).card : ℝ) = (Λ.card : ℝ) ^ 2 := by
    exact_mod_cast sum_card_shift Λ D hD
  have hsle : ∀ h : ℤ, ((Λ.filter (fun ℓ => ℓ + h ∈ Λ)).card : ℝ) ≤ Λ.card := fun h => by
    exact_mod_cast Finset.card_filter_le _ _
  set n : ℝ := (Λ.card : ℝ) with hn
  set η : ℝ := n ^ 2 / (2 * D.card) with hη
  set s : ℤ → ℕ := fun h => (Λ.filter (fun ℓ => ℓ + h ∈ Λ)).card with hs
  refine ⟨D.filter (fun h => η ≤ s h), Finset.filter_subset _ _, ?_, ?_⟩
  · set H := D.filter (fun h => η ≤ s h) with hH
    have hsplit := Finset.sum_filter_add_sum_filter_not D (fun h => η ≤ (s h : ℝ))
      (fun h => (s h : ℝ))
    rw [hsum] at hsplit
    have h1 : ∑ h ∈ H, (s h : ℝ) ≤ H.card * n := by
      calc ∑ h ∈ H, (s h : ℝ) ≤ ∑ _h ∈ H, n := Finset.sum_le_sum (fun h _ => hsle h)
        _ = H.card * n := by simp
    have h2 : ∑ h ∈ D.filter (fun h => ¬ η ≤ (s h : ℝ)), (s h : ℝ) ≤ n ^ 2 / 2 := by
      calc _ ≤ ∑ _h ∈ D.filter (fun h => ¬ η ≤ (s h : ℝ)), η :=
            Finset.sum_le_sum (fun h hh => (not_le.mp (Finset.mem_filter.mp hh).2).le)
        _ = (D.filter (fun h => ¬ η ≤ (s h : ℝ))).card * η := by simp
        _ ≤ D.card * η := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_filter_le _ _
        _ = n ^ 2 / 2 := by rw [hη]; field_simp
    have h3 : n ^ 2 / 2 ≤ H.card * n := by linarith
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  · intro h hh
    exact (Finset.mem_filter.mp hh).2

end PrimeCarleson.Proof.Fplus31
