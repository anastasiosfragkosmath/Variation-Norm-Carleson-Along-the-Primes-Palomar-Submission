module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Large
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Pigeonhole

/-!
# Symbol-level extrapolation from many dilates to the undilated symbol

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). Over the graded step-two Lie algebra `(g₁, g₂, β)` of `Model.lean`,
with the group `SymbolGroup a`, the dilations `δ_t`, the graded subalgebras `GradedSubalg a`,
`D = derived a = β(g₁, g₁)` and the data `Datum` of `Datum.lean`:

`symbol_dilation_extrapolation`.  There is an absolute `C` such that: if `d = dim g ≤ p`, the
structure constants have log-height at most `p`, `0 < c ≤ 1`, `1 ≤ q ≤ e^p`, `Λ ⊆ (L/2, L]` has
`|Λ| ≥ c L`, `A ≥ exp (C (p + log (1/c))³)`, and for every `ℓ ∈ Λ` the symbol `δ_{qℓ} X` has a
datum `(W_ℓ; A, e^p, m_ℓ)` with `m_ℓ ≤ e^p`, then for some `ℓ ∈ Λ` the undilated `X` has a datum
`(W_ℓ + D; A L / 2, e^{C B⁴}, m')` with `m' ≤ e^{C B⁴}`, `B = p + log (1/c)`.  The subalgebra
`W = W_ℓ` is exposed (`β(W₁, W₁) ⊆ W₂`).

The proof: Step 0 (small `L`: undilate a single `ℓ`, `Datum.of_dil`), Step 1 (pigeonhole over the
data, `exists_common_class`), Steps 2-4 (`large_case`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- `C_V δ^{-C_V} ≤ e^w` for `δ = e^{-(λ + 5 p³)}` and `w = C_V (1 + λ + 5 p³)`. -/
theorem V_le_exp {CV : ℕ} {p lam δ : ℝ} (hδ : δ = Real.exp (-(lam + 5 * p ^ 3))) :
    (CV : ℝ) * (δ ^ CV)⁻¹ ≤ Real.exp (CV * (1 + lam + 5 * p ^ 3)) := by
  have hδC : (δ ^ CV)⁻¹ = Real.exp (CV * (lam + 5 * p ^ 3)) := by
    rw [hδ, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  rw [hδC]
  have h1 : (CV : ℝ) ≤ Real.exp CV := by linarith [Real.add_one_le_exp (CV : ℝ)]
  calc (CV : ℝ) * Real.exp (CV * (lam + 5 * p ^ 3))
      ≤ Real.exp CV * Real.exp (CV * (lam + 5 * p ^ 3)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = Real.exp (CV * (1 + lam + 5 * p ^ 3)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Extrapolation, one variable (`s = 2`).** See the module documentation. -/
theorem symbol_dilation_extrapolation :
    ∃ C : ℝ, ∀ {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (a : Step2Algebra ι₁ ι₂) (p : ℝ),
      ((Fintype.card ι₁ + Fintype.card ι₂ : ℕ) : ℝ) ≤ p →
      (∀ i j k, ratLogHeight (a.c i j k) ≤ p) →
      ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.exp p →
      ∀ L : ℕ, 1 ≤ L → ∀ Λ : Finset ℕ, (∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) →
      c * L ≤ Λ.card → ∀ A : ℝ, Real.exp (C * (p + Real.log (1 / c)) ^ 3) ≤ A →
      ∀ (X : SymbolGroup a) (W : ℕ → GradedSubalg a) (m : ℕ → ℕ),
      (∀ ℓ ∈ Λ, (m ℓ : ℝ) ≤ Real.exp p ∧
        Datum p (W ℓ) A (Real.exp p) (m ℓ) (SymbolGroup.dil ((q : ℝ) * ℓ) X)) →
      ∃ ℓ ∈ Λ, ∃ m' : ℕ, (m' : ℝ) ≤ Real.exp (C * (p + Real.log (1 / c)) ^ 4) ∧
        (∀ x ∈ (W ℓ).layer₁, ∀ y ∈ (W ℓ).layer₁, a.br x y ∈ (W ℓ).layer₂) ∧
        Datum p (W ℓ).plusDerived (A * L / 2) (Real.exp (C * (p + Real.log (1 / c)) ^ 4)) m' X := by
  obtain ⟨CV, hCV1, hV⟩ := exists_vinoSpec_pos
  refine ⟨14 * (CV : ℝ) + 20, ?_⟩
  intro ι₁ ι₂ _ _ a p hd hc c hc0 hc1 q hq1 hq L hL1 Λ hΛ hcard A hA X W m hdat
  classical
  have hcv1 : (1 : ℝ) ≤ CV := by exact_mod_cast hCV1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hp0 : 0 ≤ p := le_trans (Nat.cast_nonneg _) hd
  have hΛne : Λ.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Λ.card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast this
  obtain ⟨ℓ₀, hℓ₀⟩ := hΛne
  set lam : ℝ := Real.log (1 / c) with hlamdef
  have hlam : 0 ≤ lam := Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  set B : ℝ := p + lam with hB
  have hB0 : 0 ≤ B := by linarith
  have hB40 : 0 ≤ B ^ 4 := by positivity
  by_cases hd0 : Fintype.card ι₁ + Fintype.card ι₂ = 0
  · -- the trivial group
    have h1 : IsEmpty ι₁ := Fintype.card_eq_zero_iff.mp (by omega)
    have h2 : IsEmpty ι₂ := Fintype.card_eq_zero_iff.mp (by omega)
    obtain ⟨-, hD⟩ := hdat ℓ₀ hℓ₀
    obtain ⟨hgen, -⟩ := hD
    refine ⟨ℓ₀, hℓ₀, 1, ?_, fun x hx y hy => (W ℓ₀).br_mem_layer₂ hx hy, ?_⟩
    · rw [Nat.cast_one]
      exact Real.one_le_exp (by positivity)
    · refine ⟨(W ℓ₀).gen_plusDerived hp0 hgen hc, one_pos, 1, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    have : (1 : ℝ) ≤ ((Fintype.card ι₁ + Fintype.card ι₂ : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
    linarith
  obtain ⟨hB1, hpB, hlB, hB3, hB4, hp3B, h7, h8⟩ := arith_facts hp1 hlam hB
  set δ : ℝ := Real.exp (-(lam + 5 * p ^ 3)) with hδdef
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    have : 0 ≤ lam + 5 * p ^ 3 := by positivity
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hVw := V_le_exp (CV := CV) hδdef
  have hCc1 : (1 : ℝ) ≤ 14 * (CV : ℝ) + 20 := by linarith
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
  by_cases hsmall : (L : ℝ) < (CV : ℝ) * (δ ^ CV)⁻¹
  · -- Step 0: a single dilate
    obtain ⟨hmℓ, hD⟩ := hdat ℓ₀ hℓ₀
    have hℓ₀pos : (0 : ℝ) < ℓ₀ := lt_trans (by positivity) (hΛ ℓ₀ hℓ₀).1
    have hD' := Datum.of_dil (q * ℓ₀) (Nat.mul_pos hq1 (by exact_mod_cast hℓ₀pos)) hApos
      (by rw [Nat.cast_mul]; exact hD)
    have hD'' := hD'.toPlusDerived hp0 hc
    have hqℓ : (L : ℝ) / 2 ≤ ((q * ℓ₀ : ℕ) : ℝ) := by
      have : (ℓ₀ : ℝ) ≤ ((q * ℓ₀ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left ℓ₀ hq1
      linarith [(hΛ ℓ₀ hℓ₀).1]
    refine ⟨ℓ₀, hℓ₀, m ℓ₀ * (q * ℓ₀) ^ 2, ?_, fun x hx y hy => (W ℓ₀).br_mem_layer₂ hx hy, ?_⟩
    · have hℓL : (ℓ₀ : ℝ) ≤ L := (hΛ ℓ₀ hℓ₀).2
      have hℓV : (ℓ₀ : ℝ) ≤ Real.exp (CV * (1 + lam + 5 * p ^ 3)) :=
        (hℓL.trans hsmall.le).trans hVw
      have hE4 := arith_E4 hcv1 hp1 hlam hB
      push_cast
      calc (m ℓ₀ : ℝ) * ((q : ℝ) * ℓ₀) ^ 2
          ≤ Real.exp p * (Real.exp p * Real.exp (CV * (1 + lam + 5 * p ^ 3))) ^ 2 := by
            gcongr
        _ = Real.exp (3 * p + 2 * (CV * (1 + lam + 5 * p ^ 3))) := by
            simp only [sq, ← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp ((14 * (CV : ℝ) + 20) * B ^ 4) := by
            apply Real.exp_le_exp.mpr
            have : (14 * (CV : ℝ) + 3) * B ^ 4 ≤ (14 * (CV : ℝ) + 20) * B ^ 4 :=
              mul_le_mul_of_nonneg_right (by linarith) hB40
            linarith
    · refine hD''.mono le_rfl (by positivity) ?_ (Real.exp_pos _).le ?_
      · have := mul_le_mul_of_nonneg_left hqℓ hApos.le
        linarith
      · apply Real.exp_le_exp.mpr
        calc p ≤ B := hpB
          _ ≤ B ^ 4 := hB3.trans hB4
          _ ≤ (14 * (CV : ℝ) + 20) * B ^ 4 := by
            nlinarith [pow_nonneg hB0 4]
  · -- Steps 1-4: a common class of dilates
    have hLV : (CV : ℝ) * (δ ^ CV)⁻¹ ≤ L := not_lt.mp hsmall
    have hv : ∀ ℓ, ∃ v : Fin (Fintype.card ι₁ + Fintype.card ι₂) → (ι₁ → ℚ) × (ι₂ → ℚ),
        ℓ ∈ Λ → (Submodule.span ℚ (Set.range v) = (W ℓ).toSubmodule ∧
          ∀ r, (∀ i, ratLogHeight ((v r).1 i) ≤ p) ∧ ∀ k, ratLogHeight ((v r).2 k) ≤ p) := by
      intro ℓ
      by_cases hℓ : ℓ ∈ Λ
      · obtain ⟨v, hv1, hv2⟩ := (hdat ℓ hℓ).2.1
        exact ⟨v, fun _ => ⟨hv1, hv2⟩⟩
      · exact ⟨fun _ => 0, fun h => absurd h hℓ⟩
    choose v hv using hv
    have hm' : ∀ ℓ ∈ Λ, 0 < m ℓ ∧ (m ℓ : ℝ) ≤ Real.exp p :=
      fun ℓ hℓ => ⟨(hdat ℓ hℓ).2.2.1, (hdat ℓ hℓ).1⟩
    have hexp : Real.exp (5 * p ^ 3) * δ = c := by
      rw [hδdef, ← Real.exp_add]
      have : 5 * p ^ 3 + -(lam + 5 * p ^ 3) = -lam := by ring
      rw [this, Real.exp_neg, hlamdef, Real.exp_log (one_div_pos.mpr hc0), one_div, inv_inv]
    have hb : Real.exp (5 * p ^ 3) * (δ * L) ≤ Λ.card := by
      calc Real.exp (5 * p ^ 3) * (δ * L) = c * L := by rw [← mul_assoc, hexp]
        _ ≤ Λ.card := hcard
    obtain ⟨Λ₁, hΛ₁sub, hΛ₁card, v₀, m₀, hΛ₁eq⟩ := exists_common_class (ι₁ := ι₁) (ι₂ := ι₂)
      hp1 hd v m (fun ℓ hℓ => (hv ℓ hℓ).2) hm' (by positivity) hb
    have hΛ₁ne : Λ₁.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < Λ₁.card := lt_of_lt_of_le (by positivity) hΛ₁card
      exact_mod_cast this
    obtain ⟨ℓ₁, hℓ₁⟩ := hΛ₁ne
    have hWeq : ∀ ℓ ∈ Λ₁, W ℓ = W ℓ₁ := by
      intro ℓ hℓ
      apply GradedSubalg.ext'
      rw [← (hv ℓ (hΛ₁sub hℓ)).1, ← (hv ℓ₁ (hΛ₁sub hℓ₁)).1, (hΛ₁eq ℓ hℓ).1, (hΛ₁eq ℓ₁ hℓ₁).1]
    have hmeq : ∀ ℓ ∈ Λ₁, m ℓ = m ℓ₁ := fun ℓ hℓ => (hΛ₁eq ℓ hℓ).2.trans (hΛ₁eq ℓ₁ hℓ₁).2.symm
    obtain ⟨hmℓ₁, hD₁⟩ := hdat ℓ₁ (hΛ₁sub hℓ₁)
    obtain ⟨m', hm'b, hDat⟩ := large_case hCV1 hV hp1 hlam hd hc le_rfl hδdef hA hq1 hq hL1 hLV
      (fun ℓ hℓ => hΛ ℓ (hΛ₁sub hℓ)) hΛ₁card X (W ℓ₁) hD₁.1 hD₁.2.1 hmℓ₁ (by
        intro ℓ hℓ
        obtain ⟨-, -, E, P, R, hprod, h1, h2, h3, h4, h5⟩ := (hdat ℓ (hΛ₁sub hℓ)).2
        refine ⟨E, P, R, hprod, h1, h2, ?_, ?_, ?_⟩
        · rw [← hmeq ℓ hℓ]
          exact h3
        · rw [← hmeq ℓ hℓ]
          exact h4
        · rw [← hWeq ℓ hℓ]
          exact h5)
    exact ⟨ℓ₁, hΛ₁sub hℓ₁, m', hm'b, fun x hx y hy => (W ℓ₁).br_mem_layer₂ hx hy, hDat⟩

end PrimeCarleson.Proof.Fplus31
