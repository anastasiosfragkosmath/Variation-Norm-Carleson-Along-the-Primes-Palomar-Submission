module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Lift
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Arith

/-!
# The large-`L` case of the extrapolation step (Steps 2, 3 and 4 together)

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). `large_case`: the dilates `ℓ ∈ Λ₁ ⊆ (L/2, L]`, `|Λ₁| ≥ δ L`, that
share one subalgebra `W` and one grid size `m`, with `δ = e^{-(λ + 5 p³)}` and `L ≥ C_V δ^{-C_V}`,
give a `(W + D)`-datum for `X` itself at the scale `A L / 2`, with slow constant and grid size at
most `e^{C B⁴}`, `B = p + λ`, provided `A ≥ e^{C B³}`. The proof applies the pivot structure to `W₁`
and `W₂ + D` (`exists_pivot`), the characters and Vinogradov (`character_family`) and the Cramer
lift (`reconstruct`); the numerical bookkeeping is in `Arith.lean`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- `m n H M / A' ≤ e^{3 p + 2 p³} / A'` for `m, n ≤ e^p`, `H ≤ e^{2 p³}`, `M = e^p`. -/
theorem bound_mnHM {p A' : ℝ} (hA' : 0 < A') {m n Hθ : ℝ}
    (hm : m ≤ Real.exp p) (hn0 : 0 ≤ n) (hn : n ≤ p) (hH0 : 0 ≤ Hθ)
    (hH : Hθ ≤ Real.exp (2 * p ^ 3)) :
    m * (n * (Hθ * (Real.exp p / A'))) ≤ Real.exp (3 * p + 2 * p ^ 3) / A' := by
  have hpe : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have h1 : m * (n * (Hθ * (Real.exp p / A'))) = (m * n * Hθ * Real.exp p) / A' := by ring
  rw [h1]
  apply div_le_div_of_nonneg_right _ hA'.le
  calc m * n * Hθ * Real.exp p ≤ Real.exp p * Real.exp p * Real.exp (2 * p ^ 3) * Real.exp p := by
        gcongr
        exact hn.trans hpe
    _ = Real.exp (3 * p + 2 * p ^ 3) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-- The slow bounds of the reconstructed factor from `Q V Ξ ≤ M'`. -/
theorem slow_algebra {Q V Ξ A L M' : ℝ} (hA : 0 < A) (hL : 0 < L) (hM : 0 ≤ M')
    (h : Q * V * Ξ ≤ M') :
    Q * (V * (Ξ / A) / L) ≤ M' / (A * L / 2) ∧
      Q * (V * (Ξ / A ^ 2) / L ^ 2) ≤ M' / (A * L / 2) ^ 2 := by
  have hAL : 0 < A * L := by positivity
  constructor
  · have e : Q * (V * (Ξ / A) / L) = (Q * V * Ξ) / (A * L) := by field_simp
    rw [e]
    exact div_le_div₀ hM h (by positivity) (by linarith)
  · have e : Q * (V * (Ξ / A ^ 2) / L ^ 2) = (Q * V * Ξ) / (A * L) ^ 2 := by field_simp
    rw [e]
    exact div_le_div₀ hM h (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)

/-- **The large-`L` case.**  See the module documentation. -/
theorem large_case {CV : ℕ} (hCV : 1 ≤ CV) (hV : VinoSpec CV) {a : Step2Algebra ι₁ ι₂}
    {p lam Cc δ A : ℝ} (hp : 1 ≤ p) (hlam : 0 ≤ lam)
    (hd : ((Fintype.card ι₁ + Fintype.card ι₂ : ℕ) : ℝ) ≤ p)
    (hc : ∀ i j k, ratLogHeight (a.c i j k) ≤ p) (hCc : 14 * (CV : ℝ) + 20 ≤ Cc)
    (hδ : δ = Real.exp (-(lam + 5 * p ^ 3)))
    (hA : Real.exp (Cc * (p + lam) ^ 3) ≤ A) {q : ℕ} (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Real.exp p)
    {L : ℕ} (hL1 : 1 ≤ L) (hLV : (CV : ℝ) * (δ ^ CV)⁻¹ ≤ L) {Λ₁ : Finset ℕ}
    (hΛ₁ : ∀ ℓ ∈ Λ₁, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) (hcard : δ * L ≤ Λ₁.card)
    (X : SymbolGroup a) (W : GradedSubalg a) (hW : W.Gen p) {m : ℕ} (hm0 : 0 < m)
    (hm : (m : ℝ) ≤ Real.exp p)
    (hdat : ∀ ℓ ∈ Λ₁, ∃ E P R : SymbolGroup a,
      E * P * R = SymbolGroup.dil ((q : ℝ) * ℓ) X ∧
      (∀ i, |E.fst i| ≤ Real.exp p / A) ∧ (∀ k, |E.snd k| ≤ Real.exp p / A ^ 2) ∧
      (∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.fst i) ∧
      (∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.snd k) ∧ (P.fst, P.snd) ∈ realSpan W.toSubmodule) :
    ∃ m' : ℕ, (m' : ℝ) ≤ Real.exp (Cc * (p + lam) ^ 4) ∧
      Datum p W.plusDerived (A * L / 2) (Real.exp (Cc * (p + lam) ^ 4)) m' X := by
  classical
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨v₀, hv₀, hh⟩ := hW
  -- the arithmetic
  obtain ⟨hB1, hpB, hlB, hB3, hB4, hp3B, h7, h8⟩ := arith_facts hp hlam rfl
  set B := p + lam with hB
  have hcv1 : (1 : ℝ) ≤ CV := by exact_mod_cast hCV
  have hCcpos : 0 ≤ Cc := by linarith
  have hu0 : 0 ≤ lam + 5 * p ^ 3 := by positivity
  have hδ0 : 0 < δ := by rw [hδ]; exact Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hδC : (δ ^ CV)⁻¹ = Real.exp (CV * (lam + 5 * p ^ 3)) := by
    rw [hδ, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  have hδC' : δ ^ CV = Real.exp (-(CV * (lam + 5 * p ^ 3))) := by
    rw [hδ, ← Real.exp_nat_mul]
    congr 1
    ring
  -- V = C_V δ^{-C_V} ≤ e^w
  set w : ℝ := CV * (1 + lam + 5 * p ^ 3) with hw
  have hw0 : 0 ≤ w := by positivity
  have hVw : (CV : ℝ) * (δ ^ CV)⁻¹ ≤ Real.exp w := by
    rw [hδC]
    have h1 : (CV : ℝ) ≤ Real.exp CV := by linarith [Real.add_one_le_exp (CV : ℝ)]
    calc (CV : ℝ) * Real.exp (CV * (lam + 5 * p ^ 3))
        ≤ Real.exp CV * Real.exp (CV * (lam + 5 * p ^ 3)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = Real.exp w := by
          rw [← Real.exp_add, hw]
          congr 1
          ring
  have hA1 : 1 ≤ A := by
    refine le_trans ?_ hA
    exact Real.one_le_exp (by positivity)
  have hApos : 0 < A := by linarith
  -- the pivot functionals
  have hn₁ : (Fintype.card ι₁ : ℝ) ≤ p := by
    have : (Fintype.card ι₁ : ℝ) ≤ ((Fintype.card ι₁ + Fintype.card ι₂ : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι₂)]
    linarith
  have hn₂ : (Fintype.card ι₂ : ℝ) ≤ p := by
    have : (Fintype.card ι₂ : ℝ) ≤ ((Fintype.card ι₁ + Fintype.card ι₂ : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι₁)]
    linarith
  let g₁ : Fin (Fintype.card ι₁ + Fintype.card ι₂) → ι₁ → ℚ := fun r i => (v₀ r).1 i
  let g₂ : Fin (Fintype.card ι₁ + Fintype.card ι₂) ⊕ (ι₁ × ι₁) → ι₂ → ℚ :=
    Sum.elim (fun r k => (v₀ r).2 k) fun ij k => a.c ij.1 ij.2 k
  obtain ⟨Z₁, Δ₁, θ₁, z₁, hΔ₁, hΔ₁b, hθ₁b, hdiag₁, hkill₁, hspan₁, -⟩ :=
    exists_pivot hp hn₁ g₁ (fun r i => (hh r).1 i)
  obtain ⟨Z₂, Δ₂, θ₂, z₂, hΔ₂, hΔ₂b, hθ₂b, hdiag₂, hkill₂, hspan₂, -⟩ :=
    exists_pivot hp hn₂ g₂ (by
      intro k i
      rcases k with r | ij
      · exact (hh r).2 i
      · exact hc _ _ _)
  -- the error budgets
  have hΞ0 : 0 < Real.exp (3 * p + 2 * p ^ 3) := Real.exp_pos _
  have hHθ0 : 0 ≤ Real.exp (2 * p ^ 3) := (Real.exp_pos _).le
  have hε₁ : (m : ℝ) * (Fintype.card ι₁ * (Real.exp (2 * p ^ 3) * (Real.exp p / A))) ≤
      Real.exp (3 * p + 2 * p ^ 3) / A :=
    bound_mnHM hApos hm (Nat.cast_nonneg _) hn₁ hHθ0 le_rfl
  have hε₂ : (m : ℝ) * (Fintype.card ι₂ * (Real.exp (2 * p ^ 3) * (Real.exp p / A ^ 2))) ≤
      Real.exp (3 * p + 2 * p ^ 3) / A ^ 2 :=
    bound_mnHM (by positivity) hm (Nat.cast_nonneg _) hn₂ hHθ0 le_rfl
  have hK : (CV : ℝ) + 3 * p + 2 * p ^ 3 + CV * (lam + 5 * p ^ 3) ≤ Cc * B ^ 3 :=
    (arith_E3 hcv1 hp hlam hB).trans
      (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith) 3))
  have hε₁' : Real.exp (3 * p + 2 * p ^ 3) / A ≤ δ ^ CV / CV := by
    have hCVpos : (0 : ℝ) < CV := by linarith
    rw [div_le_div_iff₀ hApos hCVpos, hδC']
    have h1 : Real.exp (3 * p + 2 * p ^ 3) * CV ≤
        Real.exp (3 * p + 2 * p ^ 3) * Real.exp CV :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (CV : ℝ)]) hΞ0.le
    calc Real.exp (3 * p + 2 * p ^ 3) * CV ≤ Real.exp (3 * p + 2 * p ^ 3) * Real.exp CV := h1
      _ = Real.exp (-(CV * (lam + 5 * p ^ 3))) * Real.exp (CV + 3 * p + 2 * p ^ 3 +
            CV * (lam + 5 * p ^ 3)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-(CV * (lam + 5 * p ^ 3))) * A := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact (Real.exp_le_exp.mpr hK).trans hA
  have hε₂' : Real.exp (3 * p + 2 * p ^ 3) / A ^ 2 ≤ δ ^ CV / CV := by
    refine le_trans ?_ hε₁'
    apply div_le_div_of_nonneg_left hΞ0.le hApos
    exact le_self_pow₀ hA1 (by norm_num)
  -- the data of the dilates
  have hdat' : ∀ ℓ, ∃ E P R : SymbolGroup a, ℓ ∈ Λ₁ →
      (E * P * R = SymbolGroup.dil ((q : ℝ) * ℓ) X ∧
      (∀ i, |E.fst i| ≤ Real.exp p / A) ∧ (∀ k, |E.snd k| ≤ Real.exp p / A ^ 2) ∧
      (∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.fst i) ∧
      (∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.snd k) ∧ (P.fst, P.snd) ∈ realSpan W.toSubmodule) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ Λ₁
    · obtain ⟨E, P, R, h⟩ := hdat ℓ hℓ
      exact ⟨E, P, R, fun _ => h⟩
    · exact ⟨1, 1, 1, fun h => absurd h hℓ⟩
  choose Ef Pf Rf hEPR using hdat'
  have hbr : ∀ j ∈ Z₂, ∀ i i', ∑ k, (θ₂ j k : ℚ) * a.c i i' k = 0 :=
    fun j hj i i' => hkill₂ j hj (Sum.inr (i, i'))
  obtain ⟨Q, hQpos, hQle, hfam₁, hfam₂⟩ := character_family hV X q m hδ0 hδ1 hHθ0
    (Real.exp_pos p).le hApos hLV hε₁ hε₁' hε₂ hε₂' hΛ₁ hcard Ef Pf Rf
    (fun ℓ hℓ => (hEPR ℓ hℓ).1) (fun ℓ hℓ => (hEPR ℓ hℓ).2.1)
    (fun ℓ hℓ => (hEPR ℓ hℓ).2.2.1) (fun ℓ hℓ => (hEPR ℓ hℓ).2.2.2.1)
    (fun ℓ hℓ => (hEPR ℓ hℓ).2.2.2.2.1) Z₁ θ₁ hθ₁b Z₂ θ₂ hθ₂b hbr
    (fun ℓ hℓ j hj => fnl_fst_realSpan hv₀ (θ₁ j) (fun k => hkill₁ j hj k)
      (hEPR ℓ hℓ).2.2.2.2.2)
    (fun ℓ hℓ j hj => fnl_snd_realSpan hv₀ (θ₂ j) (fun k => hkill₂ j hj (Sum.inl k))
      (hEPR ℓ hℓ).2.2.2.2.2)
  choose! y₁ hy₁ using hfam₁
  choose! y₂ hy₂ using hfam₂
  -- the size of the common denominator `Q`
  have hV0 : (0 : ℝ) ≤ (CV : ℝ) * (δ ^ CV)⁻¹ := by positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hkZ : ((Z₁.card + Z₂.card : ℕ) : ℝ) ≤ p := by
    have h1 : Z₁.card ≤ Fintype.card ι₁ := Finset.card_le_univ _
    have h2 : Z₂.card ≤ Fintype.card ι₂ := Finset.card_le_univ _
    have h3 : ((Z₁.card + Z₂.card : ℕ) : ℝ) ≤ ((Fintype.card ι₁ + Fintype.card ι₂ : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add h1 h2
    linarith
  have hQexp : (Q : ℝ) ≤ Real.exp (p * w) := by
    calc (Q : ℝ) ≤ ((CV : ℝ) * (δ ^ CV)⁻¹) ^ (Z₁.card + Z₂.card) := hQle
      _ ≤ (Real.exp w) ^ (Z₁.card + Z₂.card) := pow_le_pow_left₀ hV0 hVw _
      _ = Real.exp ((Z₁.card + Z₂.card : ℕ) * w) := (Real.exp_nat_mul w _).symm
      _ ≤ Real.exp (p * w) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hkZ hw0)
  have hE1 := arith_E1 hcv1 hp hlam hB
  rw [← hw] at hE1
  have hB40 : 0 ≤ B ^ 4 := by positivity
  have hQVΞ : (Q : ℝ) * ((CV : ℝ) * (δ ^ CV)⁻¹) * Real.exp (3 * p + 2 * p ^ 3) ≤
      Real.exp (Cc * B ^ 4) := by
    calc (Q : ℝ) * ((CV : ℝ) * (δ ^ CV)⁻¹) * Real.exp (3 * p + 2 * p ^ 3)
        ≤ Real.exp (p * w) * Real.exp w * Real.exp (3 * p + 2 * p ^ 3) :=
          mul_le_mul (mul_le_mul hQexp hVw hV0 (Real.exp_nonneg _)) le_rfl hΞ0.le
            (by positivity)
      _ = Real.exp ((p + 1) * w + 3 * p + 2 * p ^ 3) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (Cc * B ^ 4) := by
          apply Real.exp_le_exp.mpr
          have : (14 * (CV : ℝ) + 5) * B ^ 4 ≤ Cc * B ^ 4 :=
            mul_le_mul_of_nonneg_right (by linarith) hB40
          linarith
  -- the Cramer lift
  have hN₁ : 0 < Q * q * m := Nat.mul_pos (Nat.mul_pos hQpos hq1) hm0
  have hN₂ : 0 < Q * q ^ 2 * m := Nat.mul_pos (Nat.mul_pos hQpos (pow_pos hq1 2)) hm0
  have hτ₁ : 0 ≤ (Q : ℝ) * ((CV : ℝ) * (δ ^ CV)⁻¹ * (Real.exp (3 * p + 2 * p ^ 3) / A) / L) := by
    positivity
  have hτ₂ : 0 ≤ (Q : ℝ) *
      ((CV : ℝ) * (δ ^ CV)⁻¹ * (Real.exp (3 * p + 2 * p ^ 3) / A ^ 2) / (L : ℝ) ^ 2) := by
    positivity
  obtain ⟨E', P', R', hprod', hE₁', hE₂', hR₁', hR₂', hk₁, hk₂⟩ := reconstruct X Z₁ Δ₁ hΔ₁ θ₁ z₁
    hdiag₁ Z₂ Δ₂ hΔ₂ θ₂ z₂ hdiag₂ hbr (Q * q * m) (Q * q ^ 2 * m) hN₁ hN₂ hτ₁ hτ₂ y₁ y₂
    (fun j hj => by
      have e : ((Q * q * m : ℕ) : ℝ) * fnl (θ₁ j) X.fst - y₁ j =
          (Q : ℝ) * ((q : ℝ) * m * fnl (θ₁ j) X.fst) - y₁ j := by
        push_cast
        ring
      rw [e]
      exact hy₁ j hj)
    (fun j hj => by
      have e : ((Q * q ^ 2 * m : ℕ) : ℝ) * fnl (θ₂ j) X.snd - y₂ j =
          (Q : ℝ) * ((q : ℝ) ^ 2 * m * fnl (θ₂ j) X.snd) - y₂ j := by
        push_cast
        ring
      rw [e]
      exact hy₂ j hj)
  have hmem : ∀ k, v₀ k ∈ W.toSubmodule := fun k => by
    rw [← hv₀]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hspanK₁ := inl_mem_realSpan (S := W.plusDerived.toSubmodule) (g := g₁)
    (fun k => W.le_plusDerived (W.fst_mem (v₀ k) (hmem k))) (hspan₁ P'.fst hk₁)
  have hspanK₂ := inr_mem_realSpan (S := W.plusDerived.toSubmodule) (g := g₂)
    (by
      intro k
      rcases k with r | ij
      · exact W.le_plusDerived (W.snd_mem (v₀ r) (hmem r))
      · refine W.mem_plusDerived_of_derived (z := fun k => a.c ij.1 ij.2 k) ?_
        rw [derived_eq_span]
        exact Submodule.subset_span ⟨ij, rfl⟩) (hspan₂ P'.snd hk₂)
  have hsl := slow_algebra (Q := (Q : ℝ)) (V := (CV : ℝ) * (δ ^ CV)⁻¹)
    (Ξ := Real.exp (3 * p + 2 * p ^ 3)) (A := A) (L := (L : ℝ)) (M' := Real.exp (Cc * B ^ 4))
    hApos hLpos (Real.exp_pos _).le hQVΞ
  have hq2 : (q : ℝ) ^ 2 ≤ Real.exp p * Real.exp p := by
    rw [sq]
    exact mul_le_mul hq hq (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hN₁r : (Q : ℝ) * q * m ≤ Real.exp (p * w) * Real.exp p * Real.exp p :=
    mul_le_mul (mul_le_mul hQexp hq (Nat.cast_nonneg _) (Real.exp_nonneg _)) hm
      (Nat.cast_nonneg _) (by positivity)
  have hN₂r : (Q : ℝ) * (q : ℝ) ^ 2 * m ≤ Real.exp (p * w) * (Real.exp p * Real.exp p) *
      Real.exp p :=
    mul_le_mul (mul_le_mul hQexp hq2 (by positivity) (Real.exp_nonneg _)) hm (Nat.cast_nonneg _)
      (by positivity)
  have hE2 := arith_E2 hcv1 hp hlam hB
  rw [← hw] at hE2
  refine ⟨Q * q * m * (Q * q ^ 2 * m) * Δ₁ * Δ₂, ?_, ?_⟩
  · push_cast
    calc (Q : ℝ) * q * m * ((Q : ℝ) * (q : ℝ) ^ 2 * m) * Δ₁ * Δ₂
        ≤ (Real.exp (p * w) * Real.exp p * Real.exp p) *
          (Real.exp (p * w) * (Real.exp p * Real.exp p) * Real.exp p) *
          Real.exp (2 * p ^ 3) * Real.exp (2 * p ^ 3) := by
          gcongr
      _ = Real.exp (2 * p * w + 5 * p + 4 * p ^ 3) := by
          simp only [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (Cc * B ^ 4) := by
          apply Real.exp_le_exp.mpr
          have : (14 * (CV : ℝ) + 9) * B ^ 4 ≤ Cc * B ^ 4 :=
            mul_le_mul_of_nonneg_right (by linarith) hB40
          linarith
  · refine ⟨W.gen_plusDerived hp0 ⟨v₀, hv₀, hh⟩ hc,
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN₁ hN₂) hΔ₁) hΔ₂, E', P', R', hprod',
      fun i => (hE₁' i).trans hsl.1, fun k => (hE₂' k).trans hsl.2, hR₁', hR₂', ?_⟩
    have h3 := Submodule.add_mem _ hspanK₁ hspanK₂
    simpa using h3

end PrimeCarleson.Proof.Fplus31
