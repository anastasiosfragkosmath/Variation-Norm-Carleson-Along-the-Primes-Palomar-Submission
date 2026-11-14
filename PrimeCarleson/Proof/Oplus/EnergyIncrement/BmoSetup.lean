module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.IntervalBound

/-!
# The splitting `f = f' + f''` and the families `𝒯^j` of `bmosummeasures` ([O+] L1662-L1700)

[O+] L1662-L1700: "Write `f = f' + f''` where
`|f'| ≤ 1_{F ∩ 2^{ℓ+5}J}` and `|f''| ≤ 1_{F ∖ 2^{ℓ+5}J}`. [...] Let `𝒯⁰ = {T ∈ 𝒯̃ :
(1/|I_S|) ∑_{P ∈ S} |⟨f'', φ_P⟩|² ≥ e²/16}`. For `j ≥ 1` define `𝒯^j = {T ∈ 𝒯̃ :
sup_{S' ⊂ S(T), |I_{S'}| = 2^{-j}|I_T|} (1/|I_{S'}|) ∑_{P ∈ S'} |⟨f'', φ_P⟩|² ≥ e²/16}`, the sup
over `l`-overlapping trees `S' ⊂ S(T)`. Finally `𝒯^main = 𝒯̃ ∖ (𝒯⁰ ∪ 𝒯¹ ∪ …)`."

* `HasLargeSubtree C₁ C₂ M ch g lam S d`: `S` has an `l`-overlapping subtree `S'` with
  `|I_{S'}| = 2^{-d} |I_S|` and `(1/|I_{S'}|) ∑_{P ∈ S'} |⟨g, φ_P⟩|² ≥ lam`; `𝒯^d` is
  "`HasLargeSubtree`
  at `d`" (for `d = 0` the subtree `S' = S` shows this contains the printed `𝒯⁰`, and `𝒯^main` is
  contained in the printed one: a harmless, in fact stronger, definition of the main family);
* `coeff_split`: `⟨f, φ_P⟩ = ⟨f', φ_P⟩ + ⟨f'', φ_P⟩`;
* `main_term_bounds` (in `BmoMain.lean`): for `T ∈ 𝒯^main` the three facts of L1692-L1700
  for `f'`:
  `∑_{P ∈ S} |⟨f', φ_P⟩|² ≤ (17/8) e² |I_S|`, `|⟨f', φ_P⟩|² ≤ (17/8) e² |I_P|` (the energy bound for
  the single multitiles `S' = {P}`), `∑_{P ∈ S} |⟨f', φ_P⟩|² ≥ (e²/16) |I_S|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

section Split

variable {ρ : Idx}

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_sq_add_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a + b)]

/-- **`⟨f, φ_P⟩ = ⟨f', φ_P⟩ + ⟨f'', φ_P⟩`** for `f' = 1_D f`, `f'' = 1_{Dᶜ} f` and a bounded
measurable `f`. -/
theorem coeff_split (ch : ProfileChoice) {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ᵐ x, ‖f x‖ ≤ 1) {D : Set ℝ} (hD : MeasurableSet D) (P : Multitile ρ) :
    P.coeff ch f = P.coeff ch (D.indicator f) + P.coeff ch (Dᶜ.indicator f) := by
  have hf'm : AEStronglyMeasurable (D.indicator f) volume := hfm.indicator hD
  have hf''m : AEStronglyMeasurable (Dᶜ.indicator f) volume := hfm.indicator hD.compl
  have hf'b : ∀ᵐ x, ‖D.indicator f x‖ ≤ 1 := by
    filter_upwards [hf] with x hx
    by_cases h : x ∈ D
    · simpa [h] using hx
    · simp [h]
  have hf''b : ∀ᵐ x, ‖Dᶜ.indicator f x‖ ≤ 1 := by
    filter_upwards [hf] with x hx
    by_cases h : x ∈ D
    · simp [h]
    · simpa [h] using hx
  have hi1 : Integrable (fun x => D.indicator f x * (starRingEnd ℂ) (P.wavePacket ch x)) :=
    integrable_mul_conj_wavePacketOf_of_bdd ch.isProfile hf'm hf'b P.I P.ωu
  have hi2 : Integrable (fun x => Dᶜ.indicator f x * (starRingEnd ℂ) (P.wavePacket ch x)) :=
    integrable_mul_conj_wavePacketOf_of_bdd ch.isProfile hf''m hf''b P.I P.ωu
  unfold Multitile.coeff pairing
  rw [← integral_add hi1 hi2]
  congr 1; funext x
  have := congrFun (Set.indicator_self_add_compl D f) x
  rw [← this, Pi.add_apply]; ring

end Split

section Subtree

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {ch : ProfileChoice}

/-- `S` has an `l`-overlapping subtree `S'` with `|I_{S'}| = |I_S|/2^d` and
`(1/|I_{S'}|) ∑_{P ∈ S'} |⟨g, φ_P⟩|² ≥ lam`. -/
def HasLargeSubtree (C₁ C₂ : ℝ) (M : ℤ) (ch : ProfileChoice) (g : ℝ → ℂ) (lam : ℝ)
    (S : MultitileTree ρ) (d : ℕ) : Prop :=
  ∃ S' : MultitileTree ρ, S'.IsTree C₁ C₂ M ∧ S'.IsOverlapping C₂ ∧
    (S'.T : Set (Multitile ρ)) ⊆ S.T ∧ S'.I.length = S.I.length / 2 ^ d ∧
    lam * S'.I.length ≤ ∑ P ∈ S'.T, ‖P.coeff ch g‖ ^ 2

/-- A tree `S` itself is a subtree at `d = 0`. -/
theorem HasLargeSubtree.of_self {g : ℝ → ℂ} {lam : ℝ} {S : MultitileTree ρ}
    (hT : S.IsTree C₁ C₂ M) (hov : S.IsOverlapping C₂)
    (h : lam * S.I.length ≤ ∑ P ∈ S.T, ‖P.coeff ch g‖ ^ 2) :
    HasLargeSubtree C₁ C₂ M ch g lam S 0 :=
  ⟨S, hT, hov, fun _ hP => hP, by simp, h⟩

/-- **A multitile of a tree without large subtrees is small**: if `P ∈ S` (a tree whose top
interval is `I_S`) and `S` has no large subtree at `d = (k_{I_S} - k_{I_P})`, then
`|⟨g, φ_P⟩|² < lam |I_P|` (the single multitile is an `l`-overlapping tree `S' = {P}`). -/
theorem norm_sq_coeff_lt_of_not_hasLargeSubtree (hC : AdmissibleConstants C₁ C₂ C₃)
    (hρ : ρ.IsStd) {g : ℝ → ℂ} {lam : ℝ} {S : MultitileTree ρ} (hS : S.IsTree C₁ C₂ M)
    {P : Multitile ρ} (hP : P ∈ S.T) (hPsq : P.InSquare M)
    (hno : ∀ d : ℕ, ¬ HasLargeSubtree C₁ C₂ M ch g lam S d) :
    ‖P.coeff ch g‖ ^ 2 < lam * P.I.length := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨S', hT, hI, hS'tree, hov⟩ := exists_singleton_tree hC hρ hPsq
  refine hno ((S.I.k - P.I.k).toNat) ⟨S', hS'tree, hov, ?_, ?_, ?_⟩
  · intro Q hQ
    rw [hT, Finset.coe_singleton, mem_singleton_iff] at hQ
    rw [hQ]; exact hP
  · rw [hI, Dyadic.length_eq_mul_half_pow (hS.time P hP)]
    rw [one_div, inv_pow, div_eq_mul_inv]
  · rw [hT, hI, Finset.sum_singleton]
    exact hcon

end Subtree

end PrimeCarleson.Proof.Oplus
