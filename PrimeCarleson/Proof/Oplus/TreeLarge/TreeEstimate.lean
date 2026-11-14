module

public import PrimeCarleson.Proof.Oplus.TreeLarge.Special
public import PrimeCarleson.Proof.Oplus.TreeLarge.Reduction

/-!
# The tree estimate `treeestimate` ([O+] Proposition `treeestimate`, L2031-L2445)

[O+] L2031-L2044: for `ene > 0`, `0 < den < 3` and a tree `T`
with energy at most `ene` and density at most `den`, and `1 ≤ q ≤ 2`,

* (Lqfortree) `‖∑_{P ∈ T} ⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q} ≲ ene den^{min(1, r'/q)} |I_T|^{1/q}`;
* (treeestimateaway) for `ℓ ≥ 0`,
  `‖∑_{P ∈ T} ⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q(ℝ ∖ 2^ℓ I_T)} ≲
  2^{-ℓ(N-10)} ene den^{min(1, r'/q)} |I_T|^{1/q}`.

`treeestimate` proves both (with one constant) for every tree, in particular every `l`-lacunary or
`l`-overlapping tree, under the conventions of the sections before (`ρ` a standard `1`- or
`2`-index, multitiles in the square `[-2^M, 2^M]²` (`P.InSquare M`), the separation assumptions
`Separated`, `energy(S) ≤ ene`, `density(S) ≤ den` for a collection `S ⊇ T`). `r > 2`, `N ≥ 11`; the
hypotheses `ene > 0` and `den < 3` of the source are not used. The constant depends on `r`, `q`, `N`
and the admissible constants `C₁, C₂, C₃` only (uniform in `ene, den, T, f, E`, the linearizing data
and `ℓ`).

Proof (L2054-L2150): `exists_special_decomposition` splits `T` into at most `1 + 2(2⌈C₂⌉ + 1)`
special trees with the same top data (the reduction to special trees);
`treeestimate_special_pow` gives (Lqfortree) for each of them (small intervals, large intervals,
and (treeestimateaway) for `ℓ = 4`) and Minkowski's inequality sums them; (treeestimateaway) is
`treeestimate_away_from_top` for `ℓ ≥ 4` and follows from (Lqfortree) for `ℓ < 4` (the source does
not say so; this is minor).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

open PrimeCarleson PrimeCarleson.Proof.Common

section Final

variable {C₁ C₂ C₃ : ℝ}

/-- **`treeestimate`** ([O+] Proposition `treeestimate`, with the reduction to special trees, the
estimate away from the top and the assembly). Let `r > 2`, `1 ≤ q ≤ 2`, `N ≥ 11` and `C₁, C₂, C₃`
admissible constants. There is `K ≥ 0` such that for every standard `1`- or `2`-index `ρ`, profile
choice, function `f`, measurable `E`, linearizing data `L`, collection `S` of `ρ`-multitiles and
`ene, den ≥ 0` with `energy(S) ≤ ene`, `density(S) ≤ den`, and every tree `𝒯` (in particular every
`l`-lacunary or `l`-overlapping tree) of multitiles of `S` in the square `[-2^M, 2^M]²` satisfying
the separation assumptions: (a)
`‖∑_{P ∈ T} ⟨f, φ_P⟩ φ_P a_P 1_E‖_{L^q(ℝ)} ≤ K ene den^{min(1, r'/q)} |I_T|^{1/q}`; (b) for every
`ℓ ∈ ℕ`, the `L^q(ℝ ∖ 2^ℓ I_T)` norm of the same sum is at most
`K 2^{-ℓ(N-10)} ene den^{min(1, r'/q)} |I_T|^{1/q}`. -/
theorem treeestimate {r q : ℝ} (hr : 2 < r) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (N : ℕ) (hN : 11 ≤ N)
    (hC : AdmissibleConstants C₁ C₂ C₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ : Idx} [Fact ρ.IsOneOrTwo] {M : ℤ}, ρ.IsStd → ∀ (ch : ProfileChoice)
      (f : ℝ → ℂ) {E : Set ℝ}, MeasurableSet E → ∀ (L : Linearization r) {S : Set (Multitile ρ)}
      {ene den : ℝ}, 0 ≤ ene → 0 ≤ den → energy C₁ C₂ M ch f S ≤ ENNReal.ofReal ene →
      density C₁ C₂ M L E S ≤ ENNReal.ofReal den → ∀ (𝒯 : MultitileTree ρ),
      𝒯.IsTree C₁ C₂ M → (∀ P ∈ 𝒯.T, P.InSquare M) → (𝒯.T : Set (Multitile ρ)) ⊆ S →
      Separated C₁ C₂ C₃ (𝒯.T : Set (Multitile ρ)) →
        eLpNorm (treeSum ch f L E 𝒯.T) (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal (K * ene * den ^ (min 1 (Real.conjExponent r / q)) *
            𝒯.I.length ^ (1 / q)) ∧
        ∀ ℓ : ℕ, eLpNorm (treeSum ch f L E 𝒯.T) (ENNReal.ofReal q)
            (volume.restrict (𝒯.I.dilate ((2 : ℝ) ^ ℓ))ᶜ) ≤
          ENNReal.ofReal (K * ((2 : ℝ) ^ ℓ) ^ (-((N : ℤ) - 10)) * ene *
            den ^ (min 1 (Real.conjExponent r / q)) * 𝒯.I.length ^ (1 / q)) := by
  classical
  have hq0 : 0 < q := by linarith
  obtain ⟨K₀, hK₀, hK₀'⟩ := treeestimate_special_pow hr hq1 hq2 N hN hC
  obtain ⟨Kaw, hKaw0, hKaw⟩ := treeestimate_away_from_top hr.le hq1 hq2 N hN hC
  set n₀ : ℝ := 1 + 2 * (2 * ⌈C₂⌉₊ + 1) with hn₀
  have hn₀0 : 0 ≤ n₀ := by positivity
  set m : ℕ := N - 10 with hm
  have hmN : (-((N : ℤ) - 10)) = -(m : ℤ) := by rw [hm]; omega
  refine ⟨max Kaw (n₀ * K₀ * 8 ^ m), le_max_of_le_left hKaw0, ?_⟩
  intro ρ _ M hρ ch f E hE L S ene den hene hden hen hde 𝒯 hT hsq hsub hsep
  set σ := min 1 (Real.conjExponent r / q) with hσ
  have hσ0 : 0 ≤ σ := by
    refine le_min zero_le_one ?_
    have : 0 < Real.conjExponent r := by
      unfold Real.conjExponent
      exact div_pos (by linarith) (by linarith)
    positivity
  set B : ℝ := ene * den ^ σ with hB
  have hB0 : 0 ≤ B := by positivity
  have hIpos := 𝒯.I.length_pos
  have hI0 : 0 ≤ 𝒯.I.length ^ (1 / q) := by positivity
  set F := treeSum ch f L E 𝒯.T with hF
  -- (a) via the decomposition into special trees
  have ha : eLpNorm F (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (n₀ * K₀ * B * 𝒯.I.length ^ (1 / q)) := by
    obtain ⟨Λ, hcard, hlab, hspec⟩ := exists_special_decomposition (𝒯 := 𝒯) hC
    set Fl : Option (ℤ × Bool) → ℝ → ℂ := fun l => treeSum ch f L E
      (𝒯.T.filter fun P => treeLabel C₂ 𝒯.ξ P = l) with hFl
    have hFsum : F = ∑ l ∈ Λ, Fl l := by
      funext x
      rw [Finset.sum_apply]
      simp only [hF, hFl, treeSum]
      exact (Finset.sum_fiberwise_of_maps_to (s := 𝒯.T) (t := Λ)
        (g := fun P => treeLabel C₂ 𝒯.ξ P) hlab (fun P => P.coeff ch f * P.wavePacket ch x *
          P.aP L x * E.indicator (fun _ => (1 : ℂ)) x)).symm
    have hFlm : ∀ l, Measurable (Fl l) := fun l => measurable_treeSum ch f L hE _
    have hq1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1
    have hmink := eLpNorm_sum_le (μ := volume) (s := Λ) (f := Fl) hq1'
    have hterm : ∀ l ∈ Λ, eLpNorm (Fl l) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (K₀ * B * 𝒯.I.length ^ (1 / q)) := by
      intro l hl
      have h1 := hK₀' hρ ch f hE L hene hden hen hde (𝒯.restrict fun P => treeLabel C₂ 𝒯.ξ P = l)
        (hT.restrict _) (fun P hP => hsq P (Finset.mem_filter.1 hP).1)
        (by
          intro P hP
          exact hsub (Finset.mem_filter.1 (Finset.mem_coe.1 hP)).1)
        (hsep.mono (by
          intro P hP
          exact (Finset.mem_filter.1 (Finset.mem_coe.1 hP)).1)) (hspec l hl)
      have hmeas : AEStronglyMeasurable (Fl l) volume := (hFlm l).aestronglyMeasurable
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
        ENNReal.ofReal_ne_top hmeas, ENNReal.toReal_ofReal hq0.le]
      have h2 : ∫⁻ x, ‖Fl l x‖ₑ ^ q ≤ ENNReal.ofReal ((K₀ * B) ^ q * 𝒯.I.length) := by
        have e : K₀ * ene * den ^ σ = K₀ * B := by rw [hB]; ring
        simp only [MultitileTree.restrict_T, MultitileTree.restrict_I] at h1
        rw [e] at h1
        exact h1
      refine (ENNReal.rpow_le_rpow h2 (by positivity)).trans ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [Real.mul_rpow (by positivity) hIpos.le, ← Real.rpow_mul (by positivity),
        mul_one_div_cancel hq0.ne', Real.rpow_one]
    rw [hFsum]
    refine hmink.trans ?_
    calc ∑ l ∈ Λ, eLpNorm (Fl l) (ENNReal.ofReal q) volume
        ≤ ∑ l ∈ Λ, ENNReal.ofReal (K₀ * B * 𝒯.I.length ^ (1 / q)) :=
          Finset.sum_le_sum hterm
      _ = Λ.card * ENNReal.ofReal (K₀ * B * 𝒯.I.length ^ (1 / q)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal n₀ * ENNReal.ofReal (K₀ * B * 𝒯.I.length ^ (1 / q)) := by
          gcongr
          rw [← ENNReal.ofReal_natCast]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hn₀]
          exact_mod_cast hcard
      _ = ENNReal.ofReal (n₀ * K₀ * B * 𝒯.I.length ^ (1 / q)) := by
          rw [← ENNReal.ofReal_mul hn₀0]
          congr 1
          ring
  refine ⟨?_, fun ℓ => ?_⟩
  · refine ha.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : n₀ * K₀ ≤ max Kaw (n₀ * K₀ * 8 ^ m) :=
      le_max_of_le_right (by
        have : (1 : ℝ) ≤ 8 ^ m := one_le_pow₀ (by norm_num)
        nlinarith [mul_nonneg hn₀0 hK₀])
    calc n₀ * K₀ * B * 𝒯.I.length ^ (1 / q) = (n₀ * K₀) * ene * den ^ σ * 𝒯.I.length ^ (1 / q) := by
          rw [hB]; ring
      _ ≤ max Kaw (n₀ * K₀ * 8 ^ m) * ene * den ^ σ * 𝒯.I.length ^ (1 / q) := by gcongr
  · by_cases hℓ : 4 ≤ ℓ
    · have h := hKaw hρ ch f hE L hene hden hen hde 𝒯 hT hsq hsub hsep hℓ
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ ((2 : ℝ) ^ ℓ) ^ (-((N : ℤ) - 10)) := by positivity
      gcongr
      exact le_max_left _ _
    · rw [not_le] at hℓ
      have hmono : eLpNorm F (ENNReal.ofReal q) (volume.restrict (𝒯.I.dilate ((2 : ℝ) ^ ℓ))ᶜ) ≤
          eLpNorm F (ENNReal.ofReal q) volume := eLpNorm_mono_measure _ Measure.restrict_le_self
      refine (hmono.trans ha).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hmN, zpow_neg, zpow_natCast]
      have hpow : ((2 : ℝ) ^ ℓ) ^ m ≤ 8 ^ m := by
        have : (2 : ℝ) ^ ℓ ≤ 8 := by
          calc (2 : ℝ) ^ ℓ ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 8 := by norm_num
        exact pow_le_pow_left₀ (by positivity) this m
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ ℓ) ^ m := by positivity
      have h1 : n₀ * K₀ ≤ max Kaw (n₀ * K₀ * 8 ^ m) * (((2 : ℝ) ^ ℓ) ^ m)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        calc n₀ * K₀ * ((2 : ℝ) ^ ℓ) ^ m ≤ n₀ * K₀ * 8 ^ m := by
              exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hn₀0 hK₀)
          _ ≤ _ := le_max_right _ _
      calc n₀ * K₀ * B * 𝒯.I.length ^ (1 / q)
          = (n₀ * K₀) * ene * den ^ σ * 𝒯.I.length ^ (1 / q) := by rw [hB]; ring
        _ ≤ (max Kaw (n₀ * K₀ * 8 ^ m) * (((2 : ℝ) ^ ℓ) ^ m)⁻¹) * ene * den ^ σ *
            𝒯.I.length ^ (1 / q) := by gcongr

end Final

end PrimeCarleson.Proof.Oplus
