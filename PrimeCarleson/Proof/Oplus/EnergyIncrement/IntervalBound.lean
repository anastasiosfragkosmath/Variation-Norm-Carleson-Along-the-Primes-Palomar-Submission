module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.SquareByFct

/-!
# The interval bound and its steps ([O+] L1427-L1429, L1502-L1644)

Source: [O+], L1503–L1505; [O+] `etreeintervalbound`, L1427–L1429 (L1502-L1644), in the printed
form: sums over the selected trees `S_j`, `j < n`, of an `IsSelection` for `f` with
`energy(𝔓) ≤ e`. Each constant is one absolute constant, independent
of the index `ρ` (`1`- or `2`-index with `m, n ∈ {1, …, 4}`), the admissible constants, the
profile choice, `M`, `f`, `F`, `e`, the family and the selection.

* `IsSelection.sum_sq_le` (L1552, L1564-L1566): `∑_{P ∈ S_j} |⟨f, φ_P⟩|² ≤ e² |I_{S_j}|`;
* `squarebyfct_aux` (`squarebyfct`, L1503-L1505, multiplicative form): `e² ∑_j |I_{S_j}| ≤ K |F|`;
* `etreeintervalbound` (L1427-L1429): `∑_{j < n} |I_{T_j}| ≤ K e^{-2} |F|` (in `ℝ≥0∞`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-! ### Functions bounded by an indicator -/

/-- A measurable `f` with `|f| ≤ 1_F`, `|F| < ∞`, is in `L²` with `∫ |f|² ≤ |F|`. -/
theorem memLp_two_of_indicator_bound {f : ℝ → ℂ} {F : Set ℝ}
    (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) (hF : volume F ≠ ∞) :
    MemLp f 2 volume ∧ ∫ x, ‖f x‖ ^ 2 ≤ (volume F).toReal := by
  set F' : Set ℝ := toMeasurable volume F with hF'
  have hF'm : MeasurableSet F' := measurableSet_toMeasurable _ _
  have hF'F : volume F' = volume F := measure_toMeasurable F
  have hf' : ∀ᵐ x, ‖f x‖ ≤ F'.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hf] with x hx
    exact hx.trans (Set.indicator_le_indicator_of_subset (subset_toMeasurable _ _)
      (fun _ => zero_le_one) x)
  have hg : MemLp (F'.indicator fun _ => (1 : ℝ)) 2 volume :=
    memLp_indicator_const 2 hF'm.nullMeasurableSet 1 (Or.inr (by rwa [hF'F]))
  refine ⟨hg.mono' hfm hf', ?_⟩
  have hint : Integrable (F'.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hF'm).2 (integrableOn_const (by rwa [hF'F]))
  have h1 : ∀ᵐ x, ‖f x‖ ^ 2 ≤ F'.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hf'] with x hx
    by_cases hxF : x ∈ F'
    · rw [Set.indicator_of_mem hxF] at hx ⊢
      nlinarith [norm_nonneg (f x)]
    · rw [Set.indicator_of_notMem hxF] at hx ⊢
      have : ‖f x‖ = 0 := le_antisymm hx (norm_nonneg _)
      rw [this]; norm_num
  calc ∫ x, ‖f x‖ ^ 2 ≤ ∫ x, F'.indicator (fun _ => (1 : ℝ)) x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hint h1
    _ = (volume F).toReal := by
        rw [integral_indicator_const _ hF'm, smul_eq_mul, mul_one, Measure.real, hF'F]

section Sums

variable {ρ : Idx} {n : ℕ} {S : ℕ → MultitileTree ρ}

end Sums

/-! ### The printed statements -/

section Printed

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

/-- The multitiles of the selected trees lie in `𝔓`. -/
theorem IsSelection.mem_of_mem_S (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {j : ℕ} (hj : j < n)
    {P : Multitile ρ} (hP : P ∈ (S j).T) : P ∈ 𝔓 :=
  (mem_remainingFamily.1 (sel.S_subset_rem hj hP)).1

/-- The selected trees are pairwise disjoint (printed form). -/
theorem IsSelection.disjoint_range (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) :
    ∀ j < n, ∀ k < n, j ≠ k → Disjoint (S j).T (S k).T :=
  fun _ hj _ hk hne => sel.disjoint_S_S hj hk hne

/-- **`energy(𝔓) ≤ e` bounds the trees `S_j`**: `∑_{P ∈ S_j} |⟨f, φ_P⟩|² ≤ e² |I_{S_j}|`
(L1552, L1564-L1566). -/
theorem IsSelection.sum_sq_le (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) {j : ℕ} (hj : j < n)
    (he : 0 ≤ e) (hen : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e) :
    ∑ P ∈ (S j).T, ‖P.coeff ch f‖ ^ 2 ≤ e ^ 2 * (S j).I.length :=
  sum_norm_sq_coeff_le_of_energy_le he hen (sel.S_isTree hj) (sel.S_overlapping hj)
    (fun _ hP => Finset.mem_coe.2 (sel.mem_of_mem_S hj hP))

end Printed

section Interval

/-- **`squarebyfct`, multiplicative form** ([O+] L1503-L1556): there is an absolute constant `K`
with `e² ∑_{j < n} |I_{S_j}| ≤ K |F|` for the selected trees (`|F| < ∞`, `f` measurable with
`|f| ≤ 1_F`, `energy(𝔓) ≤ e`, `𝔓` inside the square `[-2^M, 2^M]²`). -/
theorem squarebyfct_aux : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
    AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ} {F : Set ℝ},
    AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
    volume F ≠ ∞ → ∀ {e : ℝ}, 0 < e → ∀ {𝔓 : Finset (Multitile ρ)},
    Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) → (∀ P ∈ 𝔓, P.InSquare M) →
    energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e →
    ∀ {n : ℕ} {S T : ℕ → MultitileTree ρ}, IsSelection C₁ C₂ M ch f e 𝔓 n S T →
      e ^ 2 * ∑ j ∈ Finset.range n, (S j).I.length ≤ K * (volume F).toReal := by
  classical
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_schwartzBound
  obtain ⟨Kt, hKt0, hKtl⟩ := exists_sum_length_mul_tail_le
  refine ⟨16 * (K₀ + 4 * K₀ * √Kt), by positivity,
    fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch {f} {F} hfm hfF hF {e} he {𝔓} hsep hsq hen {n} {S} {T}
      sel => ?_⟩
  obtain ⟨hg, hB⟩ := memLp_two_of_indicator_bound hfm hfF hF
  have hKt : ∀ j < n, ∑ P ∈ (S j).T, P.I.length *
      (∫ x in (S j).I.toSetᶜ, P.I.weight 3 x) ^ 2 ≤ Kt * (S j).I.length := fun j hj =>
    (hKtl hC hρ 3 le_rfl (S j) (sel.S_isTree hj)
      (hsep.mono (fun P hP => Finset.mem_coe.2 (sel.mem_of_mem_S hj hP))).prop2).2.2
  have h := sum_length_le_of_selection hC hρ hsep sel hK₀0 hK₀ hKt
    (J := Finset.range n) (fun j hj => Finset.mem_range.1 hj) hg hB he.le
    (by positivity : 0 < e ^ 2 / 4)
    (fun j hj => sel.sum_sq_le (Finset.mem_range.1 hj) he.le hen)
    (fun j hj P hP => norm_sq_coeff_le_of_energy_le hC hρ he.le hen
      (Finset.mem_coe.2 (sel.mem_of_mem_S (Finset.mem_range.1 hj) hP))
      (hsq P (sel.mem_of_mem_S (Finset.mem_range.1 hj) hP)))
    (fun j hj => (sel.large j (Finset.mem_range.1 hj)).large)
  have he2 : 0 < e ^ 2 := by positivity
  have h2 : e ^ 2 * (e ^ 2 * ∑ j ∈ Finset.range n, (S j).I.length) ≤
      e ^ 2 * (16 * (K₀ + 4 * K₀ * √Kt) * (volume F).toReal) := by nlinarith
  exact le_of_mul_le_mul_left h2 he2

/-- **`etreeintervalbound`** ([O+] L1427-L1429): there is an absolute constant `K > 0` such that
`∑_{j < n} |I_{T_j}| ≤ K e^{-2} |F|` (in `ℝ≥0∞`; `|F| = ∞` is allowed). -/
theorem etreeintervalbound : ∃ K : ℝ, 0 < K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}
    {M : ℤ}, AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ}
    {F : Set ℝ}, AEStronglyMeasurable f volume →
    (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {e : ℝ}, 0 < e →
    ∀ {𝔓 : Finset (Multitile ρ)}, Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
    (∀ P ∈ 𝔓, P.InSquare M) → energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e →
    ∀ {n : ℕ} {S T : ℕ → MultitileTree ρ}, IsSelection C₁ C₂ M ch f e 𝔓 n S T →
      ∑ j ∈ Finset.range n, ENNReal.ofReal (T j).I.length ≤
        ENNReal.ofReal (K / e ^ 2) * volume F := by
  obtain ⟨K, hK0, hK⟩ := squarebyfct_aux
  refine ⟨K + 1, by linarith, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch {f} {F} hfm hfF {e} he {𝔓} hsep hsq
    hen {n} {S} {T} sel => ?_⟩
  have he2 : 0 < e ^ 2 := by positivity
  have hsum : ∑ j ∈ Finset.range n, ENNReal.ofReal (T j).I.length =
      ENNReal.ofReal (∑ j ∈ Finset.range n, (S j).I.length) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (S j).I.length_pos.le)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [sel.T_I (Finset.mem_range.1 hj)]
  rw [hsum]
  by_cases hF : volume F = ∞
  · rw [hF, ENNReal.mul_top (by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)]
    exact le_top
  · have h := hK hC hρ ch hfm hfF hF he hsep hsq hen sel
    have hΛ : ∑ j ∈ Finset.range n, (S j).I.length ≤ (K + 1) / e ^ 2 * (volume F).toReal := by
      rw [div_mul_eq_mul_div, le_div_iff₀ he2]
      nlinarith [ENNReal.toReal_nonneg (a := volume F)]
    calc ENNReal.ofReal (∑ j ∈ Finset.range n, (S j).I.length)
        ≤ ENNReal.ofReal ((K + 1) / e ^ 2 * (volume F).toReal) := ENNReal.ofReal_le_ofReal hΛ
      _ = ENNReal.ofReal ((K + 1) / e ^ 2) * volume F := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hF]

end Interval

end PrimeCarleson.Proof.Oplus
