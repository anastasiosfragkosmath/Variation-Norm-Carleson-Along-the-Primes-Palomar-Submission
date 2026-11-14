module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.PisaTree
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoError

/-!
# The energy increment proposition ([O+] L1420-L1895)

Source: [O+] `energyincrementprop`, L1420–L1447:
"Let `e > 0`, let `|f|` be bounded above by `1_F` and let `𝔓` be a collection of multitiles with
energy bounded above by `e`. Then there is a collection of trees `𝒯` such that
`∑_{T ∈ 𝒯} |I_T| ≲ e^{-2}|F|` (etreeintervalbound) and `energy(𝔓 ∖ ⋃_{T ∈ 𝒯} T) ≤ e/2`, and
such that,
for every integer `ℓ ≥ 0`, `‖∑_{T ∈ 𝒯} 1_{2^ℓ I_T}‖_BMO ≲ 2^{2ℓ} e^{-2}` (etreebmobound).
Furthermore, if for some collection of trees `𝒯'`, `𝔓 = ⋃_{T' ∈ 𝒯'} T'` (pisauniont) then
`∑_{T ∈ 𝒯} |I_T| ≲ ∑_{T' ∈ 𝒯'} |I_{T'}|` (pisatree)."

`energy_increment` is this proposition for a *finite* family `𝔓` of `ρ`-multitiles (`ρ` any `1`- or
`2`-index with `m, n ∈ {1, …, 4}`, any profile choice), with one absolute implicit constant `K`
(independent of `ρ`, the admissible constants, the profile, `M`, `f`, `F`, `e`, `𝔓`); the collection
`𝒯` is a `Finset` of trees, each a nonempty tree inside `𝔓`. The families are in the setting of the
source's standing assumptions: `𝔓` is separated (`Separated`), lies in the square `[-2^M, 2^M]²`
(the `M = M_o + 3` of the ambient family, the top data being in `𝒳_top(M)`), and `f` is
measurable with `|f| ≤ 1_F`. The last clause (pisatree) is for `C₂ = 2`, the value used by the
source at L1875.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- **`energyincrementprop`** ([O+] L1420-L1447, proof L1449-L1895). -/
theorem energy_increment : ∃ K : ℝ, 0 < K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ}
    {M : ℤ}, AdmissibleConstants C₁ C₂ C₃ → ρ.IsStd → ∀ (ch : ProfileChoice) {f : ℝ → ℂ}
    {F : Set ℝ}, AEStronglyMeasurable f volume →
    (∀ᵐ x, ‖f x‖ ≤ F.indicator (fun _ => (1 : ℝ)) x) → ∀ {e : ℝ}, 0 < e →
    ∀ {𝔓 : Finset (Multitile ρ)}, Separated C₁ C₂ C₃ (𝔓 : Set (Multitile ρ)) →
    (∀ P ∈ 𝔓, P.InSquare M) → energy C₁ C₂ M ch f (𝔓 : Set (Multitile ρ)) ≤ ENNReal.ofReal e →
    ∃ 𝒯 : Finset (MultitileTree ρ),
      (∀ T ∈ 𝒯, T.IsTree C₁ C₂ M ∧ (T.T : Set (Multitile ρ)) ⊆ 𝔓 ∧ T.T.Nonempty) ∧
      ∑ T ∈ 𝒯, ENNReal.ofReal T.I.length ≤ ENNReal.ofReal (K / e ^ 2) * volume F ∧
      energy C₁ C₂ M ch f ((𝔓 : Set (Multitile ρ)) \ ⋃ T ∈ 𝒯, (T.T : Set (Multitile ρ))) ≤
        ENNReal.ofReal (e / 2) ∧
      (∀ ℓ : ℕ, dyadicBMO (fun x => ∑ T ∈ 𝒯, (T.I.dilate (2 ^ ℓ)).indicator
        (fun _ => (1 : ℝ)) x) ≤ ENNReal.ofReal (K * 2 ^ (2 * ℓ) / e ^ 2)) ∧
      (C₂ = 2 → ∀ 𝒯' : Finset (MultitileTree ρ), (∀ T' ∈ 𝒯', T'.IsTree C₁ C₂ M) →
        (𝔓 : Set (Multitile ρ)) = ⋃ T' ∈ 𝒯', (T'.T : Set (Multitile ρ)) →
        ∑ T ∈ 𝒯, ENNReal.ofReal T.I.length ≤
          ENNReal.ofReal K * ∑ T' ∈ 𝒯', ENNReal.ofReal T'.I.length) := by
  classical
  obtain ⟨K₁, hK₁0, hK₁⟩ := etreeintervalbound
  obtain ⟨K₂, hK₂0, hK₂⟩ := etreebmobound
  refine ⟨K₁ + K₂ + 16, by linarith, fun {ρ} _ {C₁ C₂ C₃} {M} hC hρ ch {f} {F} hfm hfF {e} he {𝔓}
    hsep hsq hen => ?_⟩
  obtain ⟨n, S, T, sel⟩ := exists_selection (C₁ := C₁) (C₂ := C₂) (M := M) (ch := ch) (f := f)
    he 𝔓
  have hinj : Set.InjOn T (↑(Finset.range n) : Set ℕ) := by
    rw [Finset.coe_range]; exact sel.T_injOn he
  refine ⟨(Finset.range n).image T, ?_, ?_, ?_, ?_, ?_⟩
  · intro T' hT'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hT'
    have hjn := Finset.mem_range.1 hj
    refine ⟨sel.T_isTree hjn, fun P hP => Finset.mem_coe.2
      (mem_remainingFamily.1 (sel.T_subset_rem hjn (Finset.mem_coe.1 hP))).1, ?_⟩
    obtain ⟨P, hP⟩ := sel.S_nonempty he hjn
    exact ⟨P, sel.S_subset_T hjn hP⟩
  · rw [Finset.sum_image hinj]
    refine (hK₁ hC hρ ch hfm hfF he hsep hsq hen sel).trans ?_
    gcongr
    linarith
  · have h1 := sel.stop
    rw [coe_remainingFamily] at h1
    convert h1 using 3
    ext P
    simp only [mem_iUnion, Finset.mem_image, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨T', ⟨j, hj, rfl⟩, hP⟩; exact ⟨j, hj, hP⟩
    · rintro ⟨j, hj, hP⟩; exact ⟨T j, ⟨j, hj, rfl⟩, hP⟩
  · intro ℓ
    have h := hK₂ hC hρ ch hfm hfF he hsep hsq hen sel ℓ
    have hfun : (fun x => ∑ T' ∈ (Finset.range n).image T, (T'.I.dilate (2 ^ ℓ)).indicator
        (fun _ => (1 : ℝ)) x) = fun x => ∑ j ∈ Finset.range n,
          ((T j).I.dilate (2 ^ ℓ)).indicator (fun _ => (1 : ℝ)) x := by
      funext x; rw [Finset.sum_image hinj]
    rw [hfun]
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have : (0 : ℝ) ≤ 2 ^ (2 * ℓ) / e ^ 2 := by positivity
    calc K₂ * 2 ^ (2 * ℓ) / e ^ 2 = K₂ * (2 ^ (2 * ℓ) / e ^ 2) := by ring
      _ ≤ (K₁ + K₂ + 16) * (2 ^ (2 * ℓ) / e ^ 2) := by gcongr; linarith
      _ = _ := by ring
  · intro hC₂ 𝒯' hT' hcov
    have hsub : ∀ T' ∈ 𝒯', (T'.T : Set (Multitile ρ)) ⊆ 𝔓 := fun T' hT'mem P hP => by
      rw [hcov]; exact Set.mem_iUnion₂.2 ⟨T', hT'mem, hP⟩
    have h := pisatree_sum hC hC₂ hρ hsep hsq he hen sel 𝒯' hT' hsub hcov.le
    rw [Finset.sum_image hinj]
    have h1 : ∑ j ∈ Finset.range n, ENNReal.ofReal (T j).I.length =
        ENNReal.ofReal (∑ j ∈ Finset.range n, (S j).I.length) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (S j).I.length_pos.le)]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [sel.T_I (Finset.mem_range.1 hj)]
    rw [h1]
    calc ENNReal.ofReal (∑ j ∈ Finset.range n, (S j).I.length)
        ≤ ENNReal.ofReal (16 * ∑ T' ∈ 𝒯', T'.I.length) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal 16 * ∑ T' ∈ 𝒯', ENNReal.ofReal T'.I.length := by
          rw [ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_sum_of_nonneg (fun T' _ => T'.I.length_pos.le)]
      _ ≤ ENNReal.ofReal (K₁ + K₂ + 16) * ∑ T' ∈ 𝒯', ENNReal.ofReal T'.I.length := by
          gcongr
          linarith

end PrimeCarleson.Proof.Oplus
