module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoSetup
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoGeometry

/-!
# The main term of `bmosummeasures` ([O+] L1688-L1738)

Source: [O+], L1689–L1691; [O+], L1709–L1714 (L1688-L1738): for the trees `T ∈ 𝒯^main` (the selected
trees `S_j` with `I_{S_j} ⊂ 2^{ℓ+1}J`, `|I_{S_j}| ≤ |J|`, none of whose subtrees `S'` carries a
large part of `f''`) the coefficients of `f' = 1_{2^{ℓ+5}J} f` satisfy the three facts of
`main_term_bounds`; "we continue to argue with exactly the same reasoning as in the proof of
(squarebyfct), replacing `f` with `f'` and `F` with `F ∩ 2^{ℓ+5}J`": this is the abstract
`sum_length_le_of_selection` (a subsequence of the selected trees, a function `g`, energy-type
bounds), stated with the measure of the set `G` bounding `|g|` as `squarebyfctanalog`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Main

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice} {f : ℝ → ℂ}
  {e : ℝ} {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T : ℕ → MultitileTree ρ}

/-- **The three facts for `f'`** (L1692-L1700): for `T_j ∈ 𝒯^main` (no `l`-overlapping subtree of
`S_j` carries `(1/|I_{S'}|) ∑ |⟨f'', φ_P⟩|² ≥ e²/16`),
`∑_{P ∈ S_j} |⟨f', φ_P⟩|² ≤ (17/8) e² |I_{S_j}|`, `|⟨f', φ_P⟩|² ≤ (17/8) e² |I_P|` for `P ∈ S_j`,
and `∑_{P ∈ S_j} |⟨f', φ_P⟩|² ≥ (e²/16) |I_{S_j}|`. -/
theorem main_term_bounds (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd)
    (hsq : ∀ P ∈ 𝔓, P.InSquare M) (sel : IsSelection C₁ C₂ M ch f e 𝔓 n S T) (he : 0 < e)
    (hen : energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e)
    (hfm : AEStronglyMeasurable f volume) (hf1 : ∀ᵐ x, ‖f x‖ ≤ 1) {D : Set ℝ}
    (hD : MeasurableSet D) {j : ℕ} (hj : j < n)
    (hno : ∀ d : ℕ, ¬ HasLargeSubtree C₁ C₂ M ch (Dᶜ.indicator f) (e ^ 2 / 16) (S j) d) :
    (∑ P ∈ (S j).T, ‖P.coeff ch (D.indicator f)‖ ^ 2 ≤ 17 / 8 * e ^ 2 * (S j).I.length) ∧
    (∀ P ∈ (S j).T, ‖P.coeff ch (D.indicator f)‖ ^ 2 ≤ 17 / 8 * e ^ 2 * P.I.length) ∧
    e ^ 2 / 16 * (S j).I.length ≤ ∑ P ∈ (S j).T, ‖P.coeff ch (D.indicator f)‖ ^ 2 := by
  have hI := (S j).I.length_pos
  have hsplit := fun P : Multitile ρ => coeff_split ch hfm hf1 hD P
  -- the pieces `f''`
  have hsmall : ∀ P ∈ (S j).T, ‖P.coeff ch (Dᶜ.indicator f)‖ ^ 2 < e ^ 2 / 16 * P.I.length :=
    fun P hP => norm_sq_coeff_lt_of_not_hasLargeSubtree hC hρ (sel.S_isTree hj) hP
      (hsq P (sel.mem_of_mem_S hj hP)) hno
  have hsum'' : ∑ P ∈ (S j).T, ‖P.coeff ch (Dᶜ.indicator f)‖ ^ 2 < e ^ 2 / 16 * (S j).I.length := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hno 0 (HasLargeSubtree.of_self (sel.S_isTree hj) (sel.S_overlapping hj) hcon)
  have hc' : ∀ P : Multitile ρ, ‖P.coeff ch (D.indicator f)‖ ^ 2 ≤
      2 * ‖P.coeff ch f‖ ^ 2 + 2 * ‖P.coeff ch (Dᶜ.indicator f)‖ ^ 2 := fun P => by
    have h := norm_sq_add_le (P.coeff ch f) (-(P.coeff ch (Dᶜ.indicator f)))
    rw [norm_neg] at h
    have e1 : P.coeff ch (D.indicator f) = P.coeff ch f + -(P.coeff ch (Dᶜ.indicator f)) := by
      rw [hsplit P]; ring
    rw [e1]; exact h
  have hc : ∀ P : Multitile ρ, ‖P.coeff ch f‖ ^ 2 ≤
      2 * ‖P.coeff ch (D.indicator f)‖ ^ 2 + 2 * ‖P.coeff ch (Dᶜ.indicator f)‖ ^ 2 := fun P => by
    have h := norm_sq_add_le (P.coeff ch (D.indicator f)) (P.coeff ch (Dᶜ.indicator f))
    rw [← hsplit P] at h; exact h
  refine ⟨?_, fun P hP => ?_, ?_⟩
  · have h1 := sel.sum_sq_le hj he.le hen
    calc ∑ P ∈ (S j).T, ‖P.coeff ch (D.indicator f)‖ ^ 2
        ≤ ∑ P ∈ (S j).T, (2 * ‖P.coeff ch f‖ ^ 2 + 2 * ‖P.coeff ch (Dᶜ.indicator f)‖ ^ 2) :=
          Finset.sum_le_sum fun P _ => hc' P
      _ = 2 * ∑ P ∈ (S j).T, ‖P.coeff ch f‖ ^ 2 +
            2 * ∑ P ∈ (S j).T, ‖P.coeff ch (Dᶜ.indicator f)‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 17 / 8 * e ^ 2 * (S j).I.length := by nlinarith
  · have hPm := sel.mem_of_mem_S hj hP
    have h1 := norm_sq_coeff_le_of_energy_le hC hρ he.le hen (Finset.mem_coe.2 hPm) (hsq P hPm)
    have h2 := hsmall P hP
    have := hc' P
    nlinarith
  · have h1 := (sel.large j hj).large
    have : ∑ P ∈ (S j).T, ‖P.coeff ch f‖ ^ 2 ≤
        2 * ∑ P ∈ (S j).T, ‖P.coeff ch (D.indicator f)‖ ^ 2 +
          2 * ∑ P ∈ (S j).T, ‖P.coeff ch (Dᶜ.indicator f)‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun P _ => hc P
    linarith

/-- **`squarebyfctanalog`** ([O+] L1709-L1737): the squared-sum inequality for a subsequence
`S_j`, `j ∈ J`, of the selected trees and a function `g` with `|g| ≤ 1_G`: if
`∑_{P ∈ S_j} |c_P|² ≤ E² |I_{S_j}|`, `|c_P|² ≤ E² |I_P|` and
`(1/|I_{S_j}|) ∑_{P ∈ S_j} |c_P|² ≥ lam`, with `c_P = ⟨g, φ_P⟩`, then
`lam² ∑_{j ∈ J} |I_{S_j}| ≤ K E² |G|`. With `lam = e²/16`, `E² = (17/8) e²`, `g = f'`,
`G = F ∩ 2^{ℓ+5}J` it reads `(e²/|G|) ∑_ν |I_{S_{j(ν)}}| ≲ 1`. -/
theorem squarebyfctanalog : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}
    {M : ℤ}, AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ} {e : ℝ}
    {𝔓 : Finset (Multitile ρ)}, Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
    ∀ {n : ℕ} {S T : ℕ → MultitileTree ρ}, IsSelection C₁ C₂ M ch f e 𝔓 n S T →
    ∀ {g : ℝ → ℂ} {G : Set ℝ}, AEStronglyMeasurable g volume →
    (∀ᵐ x, ‖g x‖ ≤ G.indicator (fun _ => (1 : ℝ)) x) → volume G ≠ ∞ →
    ∀ {J : Finset ℕ}, (∀ j ∈ J, j < n) → ∀ {lam E : ℝ}, 0 < lam → 0 ≤ E →
    (∀ j ∈ J, ∑ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2 ≤ E ^ 2 * (S j).I.length) →
    (∀ j ∈ J, ∀ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2 ≤ E ^ 2 * P.I.length) →
    (∀ j ∈ J, lam * (S j).I.length ≤ ∑ P ∈ (S j).T, ‖P.coeff ch g‖ ^ 2) →
      lam ^ 2 * ∑ j ∈ J, (S j).I.length ≤ K * E ^ 2 * (volume G).toReal := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_schwartzBound
  obtain ⟨Kt, hKt0, hKtl⟩ := exists_sum_length_mul_tail_le
  refine ⟨K₀ + 4 * K₀ * √Kt, by positivity, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch {f} {e} {𝔓} hsep
    {n} {S} {T} sel {g} {G} hgm hgG hG {J} hJ {lam} {E} hlam hE hE1 hE2 hlarge => ?_⟩
  obtain ⟨hg, hB⟩ := memLp_two_of_indicator_bound hgm hgG hG
  have hKt : ∀ j < n, ∑ P ∈ (S j).T, P.I.length *
      (∫ x in (S j).I.toSetᶜ, P.I.weight 3 x) ^ 2 ≤ Kt * (S j).I.length := fun j hj =>
    (hKtl hC hρ 3 le_rfl (S j) (sel.S_isTree hj)
      (hsep.mono (fun P hP => Finset.mem_coe.2 (sel.mem_of_mem_S hj hP))).prop2).2.2
  exact sum_length_le_of_selection hC hρ hsep sel hK₀0 hK₀ hKt hJ hg hB hE hlam hE1 hE2 hlarge

/-- `j ∈ 𝒯̃`: `I_{T_j} ⊂ 2^{ℓ+1} J` and `|I_{T_j}| ≤ |J|` (L1662-L1663). -/
def InTilde {ρ : Idx} (S : ℕ → MultitileTree ρ) (J : Dyadic) (ℓ : ℕ) (j : ℕ) : Prop :=
  (S j).I.toSet ⊆ J.dilate (2 ^ (ℓ + 1)) ∧ (S j).I.length ≤ J.length

open Classical in
/-- **`sumITinTprime`** ([O+] L1689-L1738): the main term
`∑_{T ∈ 𝒯^main} |I_T| ≤ K e^{-2} 2^ℓ |J|`. -/
theorem sumITinTprime : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ},
    AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ} {F : Set ℝ},
    AEStronglyMeasurable f volume → (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) →
    ∀ {e : ℝ}, 0 < e → ∀ {𝔓 : Finset (Multitile ρ)},
    Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) → (∀ P ∈ 𝔓, P.InSquare M) →
    energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e →
    ∀ {n : ℕ} {S T : ℕ → MultitileTree ρ}, IsSelection C₁ C₂ M ch f e 𝔓 n S T →
    ∀ (J : Dyadic) (ℓ : ℕ),
      ∑ j ∈ (Finset.range n).filter (fun j => InTilde S J ℓ j ∧ ∀ d : ℕ,
          ¬ HasLargeSubtree C₁ C₂ M ch ((J.dilate (2 ^ (ℓ + 5)))ᶜ.indicator f) (e ^ 2 / 16)
            (S j) d), (S j).I.length ≤ K / e ^ 2 * (2 ^ ℓ * J.length) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := squarebyfctanalog
  refine ⟨20000 * K₁, by positivity, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch {f} {F} hfm hfF {e} he {𝔓}
    hsep hsq hen {n} {S} {T} sel J ℓ => ?_⟩
  set D : Set ℝ := J.dilate (2 ^ (ℓ + 5)) with hDdef
  have hD : MeasurableSet D := J.measurableSet_dilate _
  have hf1 : ∀ᵐ x, ‖f x‖ ≤ 1 := by
    filter_upwards [hfF] with x hx
    exact hx.trans (Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans le_rfl)
  set Mn := (Finset.range n).filter (fun j => InTilde S J ℓ j ∧ ∀ d : ℕ,
      ¬ HasLargeSubtree C₁ C₂ M ch (Dᶜ.indicator f) (e ^ 2 / 16) (S j) d) with hMn
  have hMnn : ∀ j ∈ Mn, j < n := fun j hj => Finset.mem_range.1 (Finset.mem_filter.1 hj).1
  have hvolD : volume D = ENNReal.ofReal (2 ^ (ℓ + 5) * J.length) := J.volume_dilate _
  have hGfin : volume (F ∩ D) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hvolD]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  have hgG : ∀ᵐ x, ‖D.indicator f x‖ ≤ (F ∩ D).indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hfF] with x hx
    by_cases hxD : x ∈ D
    · rw [Set.indicator_of_mem hxD]
      by_cases hxF : x ∈ F
      · rw [Set.indicator_of_mem (show x ∈ F ∩ D from ⟨hxF, hxD⟩)]
        simpa [hxF] using hx
      · rw [Set.indicator_of_notMem (fun h => hxF h.1)]
        simpa [hxF] using hx
    · rw [Set.indicator_of_notMem hxD, Set.indicator_of_notMem (fun h => hxD h.2)]
      simp
  have hbd := fun j (hj : j ∈ Mn) => main_term_bounds hC hρ hsq sel he hen hfm hf1 hD
    (hMnn j hj) (Finset.mem_filter.1 hj).2.2
  have hE2pos : 0 ≤ √(17 / 8 * e ^ 2) := Real.sqrt_nonneg _
  have hE2sq : √(17 / 8 * e ^ 2) ^ 2 = 17 / 8 * e ^ 2 := Real.sq_sqrt (by positivity)
  have h := hK₁ hC hρ ch hsep sel (g := D.indicator f) (G := F ∩ D) (hfm.indicator hD) hgG hGfin
    (J := Mn) hMnn (lam := e ^ 2 / 16) (E := √(17 / 8 * e ^ 2)) (by positivity) hE2pos
    (fun j hj => by rw [hE2sq]; exact (hbd j hj).1.trans (le_of_eq (by ring)))
    (fun j hj P hP => by rw [hE2sq]; exact (hbd j hj).2.1 P hP |>.trans (le_of_eq (by ring)))
    (fun j hj => (hbd j hj).2.2)
  have hvolG : (volume (F ∩ D)).toReal ≤ 2 ^ (ℓ + 5) * J.length := by
    have := ENNReal.toReal_mono (by rw [hvolD]; exact ENNReal.ofReal_ne_top)
      (measure_mono (Set.inter_subset_right : F ∩ D ⊆ D))
    rw [hvolD, ENNReal.toReal_ofReal (by have := J.length_pos; positivity)] at this
    exact this
  rw [hE2sq] at h
  have he2 : 0 < e ^ 2 := by positivity
  have hJ0 := J.length_pos
  have hx0 : 0 ≤ ∑ j ∈ Mn, (S j).I.length := Finset.sum_nonneg fun j _ => (S j).I.length_pos.le
  have h2 : (e ^ 2 / 16) ^ 2 * ∑ j ∈ Mn, (S j).I.length ≤
      K₁ * (17 / 8 * e ^ 2) * (2 ^ (ℓ + 5) * J.length) :=
    h.trans (mul_le_mul_of_nonneg_left hvolG (by positivity))
  rw [div_mul_eq_mul_div, le_div_iff₀ he2]
  have h3 : (2 : ℝ) ^ (ℓ + 5) = 32 * 2 ^ ℓ := by rw [pow_add]; ring
  rw [h3] at h2
  have h4 : e ^ 2 * (e ^ 2 * ∑ j ∈ Mn, (S j).I.length) ≤
      e ^ 2 * (17408 * K₁ * (2 ^ ℓ * J.length)) := by nlinarith
  have := le_of_mul_le_mul_left h4 he2
  nlinarith [mul_nonneg hK₁0 (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ℓ) hJ0.le)]

end Main

end PrimeCarleson.Proof.Oplus
