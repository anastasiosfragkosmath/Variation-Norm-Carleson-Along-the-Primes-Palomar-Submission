module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Main
public import PrimeCarleson.Proof.Fplus31.Extrapolation.LargeII

/-!
# Extrapolation, type II variant: the product form via the `K⁰` argument

Part of the abstract extrapolation, type II variant (the extrapolation step of the iteration of
`C2/CMain.lean`, proof of [F+] Proposition 3.1). Over the model of `Model.lean`, let
`a.prod = g × g` be the product algebra and `biDil s t X = (δ_s X, δ_t X)` the pair of dilates.

`symbol_dilation_extrapolation_typeII`. There is an absolute `C` such that: if the dimension `2 d`
of the product is at most `p`, the structure constants have log-height at most `p`, `0 < c ≤ 1`,
`1 ≤ q ≤ e^p`, `L ≥ exp (C B³)` (`B = p + log (1/c)`; there is no small-`L` branch in type II),
`Γ ⊆ (L/2, L]²` has `|Γ| ≥ c L²`, `A ≥ exp (C B³)`, and for each `(ℓ, ℓ') ∈ Γ` the pair
`(δ_{qℓ} X, δ_{qℓ'} X)` has a datum `(W_{ℓℓ'}; A, e^p, m_{ℓℓ'})` in the group of `g × g`, then for
some `(ℓ, ℓ') ∈ Γ` the single factor `X` has a datum `(K⁰; A L / 2, e^{C B⁴}, m')` in the group of
`g`, with heights parameter `C B⁴`, `K⁰ = {k : (k, 0) ∈ W + D × D, (0, k) ∈ W + D × D}`
(`GradedSubalg.commonKernel`), together with the exposure `([k, k'], 0), (0, [k, k']) ∈ W₂` for
`k, k' ∈ K⁰₁` used by the descending stage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- **Extrapolation, type II (product form).** See the module documentation. -/
theorem symbol_dilation_extrapolation_typeII :
    ∃ C : ℝ, ∀ {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (a : Step2Algebra ι₁ ι₂) (p : ℝ),
      ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) ≤ p →
      (∀ i j k, ratLogHeight (a.c i j k) ≤ p) →
      ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.exp p →
      ∀ L : ℕ, Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ L →
      ∀ Γ : Finset (ℕ × ℕ),
        (∀ pr ∈ Γ, (L : ℝ) / 2 < pr.1 ∧ (pr.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < pr.2 ∧ (pr.2 : ℝ) ≤ L) →
      c * (L : ℝ) ^ 2 ≤ Γ.card → ∀ A : ℝ, Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ A →
      ∀ (X : SymbolGroup a) (W : ℕ × ℕ → GradedSubalg a.prod) (m : ℕ × ℕ → ℕ),
      (∀ pr ∈ Γ, (m pr : ℝ) ≤ Real.exp p ∧
        Datum p (W pr) A (Real.exp p) (m pr)
          (SymbolGroup.biDil ((q : ℝ) * pr.1) ((q : ℝ) * pr.2) X)) →
      ∃ pr ∈ Γ, ∃ m' : ℕ, (m' : ℝ) ≤ Real.exp (C * (p + Real.log (1 / c)) ^ 4) ∧
        (∀ k ∈ (W pr).plusDerived.commonKernel.layer₁,
          ∀ k' ∈ (W pr).plusDerived.commonKernel.layer₁,
          Sum.elim (a.br k k') (0 : ι₂ → ℚ) ∈ (W pr).layer₂ ∧
            Sum.elim (0 : ι₂ → ℚ) (a.br k k') ∈ (W pr).layer₂) ∧
        Datum (C * (p + Real.log (1 / c)) ^ 4) (W pr).plusDerived.commonKernel (A * L / 2)
          (Real.exp (C * (p + Real.log (1 / c)) ^ 4)) m' X := by
  obtain ⟨CV, hCV1, hV⟩ := exists_vino2Spec_pos
  refine ⟨14 * (CV : ℝ) + 40, ?_⟩
  intro ι₁ ι₂ _ _ a p hd hc c hc0 hc1 q hq1 hq L hL Γ hΓ hcard A hA X W m hdat
  classical
  have hcv1 : (1 : ℝ) ≤ CV := by exact_mod_cast hCV1
  have hp0 : 0 ≤ p := le_trans (Nat.cast_nonneg _) hd
  set lam : ℝ := Real.log (1 / c) with hlamdef
  have hlam : 0 ≤ lam := Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  set B : ℝ := p + lam with hB
  have hB0 : 0 ≤ B := by linarith
  have hL1' : (1 : ℝ) ≤ L := le_trans (Real.one_le_exp (by positivity)) hL
  have hL1 : 1 ≤ L := by exact_mod_cast hL1'
  have hLpos : (0 : ℝ) < L := by linarith
  have hΓne : Γ.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Γ.card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  obtain ⟨pr₀, hpr₀⟩ := hΓne
  by_cases hd0 : Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) = 0
  · -- the trivial group
    have h1 : IsEmpty ι₁ := by
      have : Fintype.card ι₁ = 0 := by rw [Fintype.card_sum] at hd0; omega
      exact Fintype.card_eq_zero_iff.mp this
    have h2 : IsEmpty ι₂ := by
      have : Fintype.card ι₂ = 0 := by rw [Fintype.card_sum, Fintype.card_sum] at hd0; omega
      exact Fintype.card_eq_zero_iff.mp this
    have hsub : ∀ w : (ι₁ → ℚ) × (ι₂ → ℚ), w = 0 := fun w =>
      Prod.ext (funext fun i => isEmptyElim i) (funext fun k => isEmptyElim k)
    have hzero : ∀ z : ι₂ ⊕ ι₂ → ℚ, z = 0 := fun z => funext fun k => by
      rcases k with k | k <;> exact isEmptyElim k
    refine ⟨pr₀, hpr₀, 1, ?_, fun k _ k' _ => ⟨?_, ?_⟩, ?_⟩
    · rw [Nat.cast_one]
      exact Real.one_le_exp (by positivity)
    · rw [hzero (Sum.elim (a.br k k') 0)]
      exact Submodule.zero_mem _
    · rw [hzero (Sum.elim 0 (a.br k k'))]
      exact Submodule.zero_mem _
    · have hcgen : (W pr₀).plusDerived.commonKernel.Gen ((14 * (CV : ℝ) + 40) * B ^ 4) := by
        refine ⟨fun _ => 0, ?_, fun r => ⟨fun i => isEmptyElim i, fun k => isEmptyElim k⟩⟩
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨r, rfl⟩
          exact Submodule.zero_mem _
        · intro w _
          rw [hsub w]
          exact Submodule.zero_mem _
      refine ⟨hcgen, one_pos, 1, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · ext1
        · exact funext fun i => isEmptyElim i
        · exact funext fun k => isEmptyElim k
      · intro i; exact isEmptyElim i
      · intro k; exact isEmptyElim k
      · intro i; exact isEmptyElim i
      · intro k; exact isEmptyElim k
      · have h3 : ((1 : SymbolGroup a).fst, (1 : SymbolGroup a).snd) = 0 := by
          exact Prod.ext (funext fun i => isEmptyElim i) (funext fun k => isEmptyElim k)
        rw [h3]
        exact Submodule.zero_mem _
  have hp1 : 1 ≤ p := by
    have : (1 : ℝ) ≤ ((Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂) : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
    linarith
  obtain ⟨hB1, hpB, hlB, hB3, hB4, hp3B, h7, h8⟩ := arith_facts hp1 hlam hB
  set δ : ℝ := Real.exp (-(lam + 5 * p ^ 3)) with hδdef
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    have : 0 ≤ lam + 5 * p ^ 3 := by positivity
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hVw := V_le_exp (CV := CV) hδdef
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
  have hLV : (CV : ℝ) * (δ ^ CV)⁻¹ ≤ L := by
    refine hVw.trans (le_trans (Real.exp_le_exp.mpr ?_) hL)
    have : (CV : ℝ) * (1 + lam + 5 * p ^ 3) ≤ CV * (7 * B ^ 3) :=
      mul_le_mul_of_nonneg_left h7 (by linarith)
    have h9 : (7 * (CV : ℝ)) * B ^ 3 ≤ (14 * (CV : ℝ) + 40) * B ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hv : ∀ pr, ∃ v : Fin (Fintype.card (ι₁ ⊕ ι₁) + Fintype.card (ι₂ ⊕ ι₂)) →
      (ι₁ ⊕ ι₁ → ℚ) × (ι₂ ⊕ ι₂ → ℚ),
      pr ∈ Γ → (Submodule.span ℚ (Set.range v) = (W pr).toSubmodule ∧
        ∀ r, (∀ i, ratLogHeight ((v r).1 i) ≤ p) ∧ ∀ k, ratLogHeight ((v r).2 k) ≤ p) := by
    intro pr
    by_cases hpr : pr ∈ Γ
    · obtain ⟨v, hv1, hv2⟩ := (hdat pr hpr).2.1
      exact ⟨v, fun _ => ⟨hv1, hv2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hpr⟩
  choose v hv using hv
  have hm' : ∀ pr ∈ Γ, 0 < m pr ∧ (m pr : ℝ) ≤ Real.exp p :=
    fun pr hpr => ⟨(hdat pr hpr).2.2.1, (hdat pr hpr).1⟩
  have hexp : Real.exp (5 * p ^ 3) * δ = c := by
    rw [hδdef, ← Real.exp_add]
    have : 5 * p ^ 3 + -(lam + 5 * p ^ 3) = -lam := by ring
    rw [this, Real.exp_neg, hlamdef, Real.exp_log (one_div_pos.mpr hc0), one_div, inv_inv]
  have hb : Real.exp (5 * p ^ 3) * (δ * (L : ℝ) ^ 2) ≤ (Γ.card : ℝ) := by
    calc Real.exp (5 * p ^ 3) * (δ * (L : ℝ) ^ 2) = c * (L : ℝ) ^ 2 := by
          rw [← mul_assoc, hexp]
      _ ≤ (Γ.card : ℝ) := hcard
  obtain ⟨Γ₁, hΓ₁sub, hΓ₁card, v₀, m₀, hΓ₁eq⟩ := exists_common_class (ι₁ := ι₁ ⊕ ι₁)
    (ι₂ := ι₂ ⊕ ι₂) hp1 hd v m (fun pr hpr => (hv pr hpr).2) hm' (by positivity) hb
  have hΓ₁ne : Γ₁.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Γ₁.card := lt_of_lt_of_le (by positivity) hΓ₁card
    exact_mod_cast this
  obtain ⟨pr₁, hpr₁⟩ := hΓ₁ne
  have hWeq : ∀ pr ∈ Γ₁, W pr = W pr₁ := by
    intro pr hpr
    apply GradedSubalg.ext'
    rw [← (hv pr (hΓ₁sub hpr)).1, ← (hv pr₁ (hΓ₁sub hpr₁)).1, (hΓ₁eq pr hpr).1,
      (hΓ₁eq pr₁ hpr₁).1]
  have hmeq : ∀ pr ∈ Γ₁, m pr = m pr₁ := fun pr hpr =>
    (hΓ₁eq pr hpr).2.trans (hΓ₁eq pr₁ hpr₁).2.symm
  obtain ⟨hmℓ₁, hD₁⟩ := hdat pr₁ (hΓ₁sub hpr₁)
  obtain ⟨m', hm'b, hDat⟩ := large_caseII hCV1 hV hp1 hlam hd hc le_rfl hδdef hA hq1 hq hL1 hLV
    (fun pr hpr => hΓ pr (hΓ₁sub hpr)) hΓ₁card X (W pr₁) hD₁.1 hD₁.2.1 hmℓ₁ (by
      intro pr hpr
      obtain ⟨-, -, E, P, R, hprod, h1, h2, h3, h4, h5⟩ := (hdat pr (hΓ₁sub hpr)).2
      refine ⟨E, P, R, hprod, h1, h2, ?_, ?_, ?_⟩
      · rw [← hmeq pr hpr]
        exact h3
      · rw [← hmeq pr hpr]
        exact h4
      · rw [← hWeq pr hpr]
        exact h5)
  exact ⟨pr₁, hΓ₁sub hpr₁, m', hm'b, fun k hk k' hk' =>
    GradedSubalg.exposure_commonKernel (W pr₁) hk hk', hDat⟩

end PrimeCarleson.Proof.Fplus31
