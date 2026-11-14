module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Characters
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Product
public import PrimeCarleson.Proof.Fplus31.Vinogradov.TypeII

/-!
# Steps 2 and 3 of the extrapolation step, type II: two-variable Vinogradov

Part of the abstract extrapolation, type II variant (the extrapolation step of the iteration of
`C2/CMain.lean`, proof of [F+] Proposition 3.1). The symbol of the pair orbit is
`(δ_{qℓ} X, δ_{qℓ'} X)` in the group of `a.prod`; a character `θ = (θ⁰, θ¹)` of the product gives
`(q ℓ) θ⁰(x₁) + (q ℓ') θ¹(x₁)` (no mixed term), and the separate-variable form of the two-variable
Vinogradov lemma (`vinogradov_two_var_separate`) gives smallness of `Q θ⁰(x₁)` and `Q θ¹(x₁)`
separately.

* `layer_one_gen`, `layer_two_gen`: the distance bounds for an arbitrary product `E P R`;
* `Vino2Spec`, `vino2_lin`, `vino2_quad`: Vinogradov for `β⁰ ℓ + β¹ ℓ'` and `β⁰ ℓ² + β¹ ℓ'²`;
* `character_family₂`: a common denominator `Q` making all the half-functionals of all the pivot
  functionals approximately integral.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {a : Step2Algebra ι₁ ι₂}

section Gen

variable {ι₁' ι₂' : Type*} [Fintype ι₁'] {a' : Step2Algebra ι₁' ι₂'}

/-- Distance bound, layer one, for an arbitrary product. -/
theorem layer_one_gen (E P R : SymbolGroup a') (m : ℕ) (θ : ι₁' → ℤ) {H M A : ℝ} (hH : 0 ≤ H)
    (hθ : ∀ i, |(θ i : ℝ)| ≤ H) (hE : ∀ i, |E.fst i| ≤ M / A)
    (hR : ∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.fst i) (hP : fnl θ P.fst = 0) :
    ‖(((m : ℝ) * fnl θ (E * P * R).fst : ℝ) : UnitAddCircle)‖ ≤
      m * (Fintype.card ι₁' * (H * (M / A))) := by
  rw [SymbolGroup.mul₃_fst, fnl_add, fnl_add, hP, add_zero]
  choose k hk using hR
  have hK : (m : ℝ) * fnl θ R.fst = ((∑ i, θ i * k i : ℤ) : ℝ) := by
    simp only [fnl, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk i]
    ring
  have hx : (m : ℝ) * (fnl θ E.fst + fnl θ R.fst) =
      m * fnl θ E.fst + ((∑ i, θ i * k i : ℤ) : ℝ) := by
    rw [← hK]
    ring
  rw [hx, norm_coe_add_intCast]
  refine (norm_coe_le_abs _).trans ?_
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  exact mul_le_mul_of_nonneg_left (abs_fnl_le θ hH hθ E.fst hE) (Nat.cast_nonneg m)

/-- Distance bound, layer two, for an arbitrary product. -/
theorem layer_two_gen [Fintype ι₂'] (E P R : SymbolGroup a') (m : ℕ) (θ : ι₂' → ℤ)
    {H M A : ℝ} (hbr : ∀ i i', ∑ k, (θ k : ℚ) * a'.c i i' k = 0) (hH : 0 ≤ H)
    (hθ : ∀ k, |(θ k : ℝ)| ≤ H) (hE : ∀ k, |E.snd k| ≤ M / A ^ 2)
    (hR : ∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.snd k) (hP : fnl θ P.snd = 0) :
    ‖(((m : ℝ) * fnl θ (E * P * R).snd : ℝ) : UnitAddCircle)‖ ≤
      m * (Fintype.card ι₂' * (H * (M / A ^ 2))) := by
  have hb := fnl_br_zero (a := a') θ hbr
  have h2 : fnl θ (E * P * R).snd = fnl θ E.snd + fnl θ R.snd := by
    rw [SymbolGroup.mul₃_snd, fnl_add, fnl_add, fnl_add, fnl_smul, fnl_add, fnl_add, hb, hb, hb, hP]
    ring
  rw [h2]
  choose k hk using hR
  have hK : (m : ℝ) * fnl θ R.snd = ((∑ i, θ i * k i : ℤ) : ℝ) := by
    simp only [fnl, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk i]
    ring
  have hx : (m : ℝ) * (fnl θ E.snd + fnl θ R.snd) =
      m * fnl θ E.snd + ((∑ i, θ i * k i : ℤ) : ℝ) := by
    rw [← hK]
    ring
  rw [hx, norm_coe_add_intCast]
  refine (norm_coe_le_abs _).trans ?_
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  exact mul_le_mul_of_nonneg_left (abs_fnl_le θ hH hθ E.snd hE) (Nat.cast_nonneg m)

end Gen

/-- A functional of the product evaluated on `(s x, t x)`. -/
theorem fnl_sumElim {ι : Type*} [Fintype ι] (θ : ι ⊕ ι → ℤ) (s t : ℝ) (x : ι → ℝ) :
    fnl θ (Sum.elim (s • x) (t • x)) =
      s * fnl (fun i => θ (.inl i)) x + t * fnl (fun i => θ (.inr i)) x := by
  simp only [fnl, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- The statement of the two-variable Vinogradov lemma (separate form) with the constant fixed. -/
def Vino2Spec (C : ℕ) : Prop :=
  ∀ (δ ε : ℝ), 0 < δ → δ ≤ 1 → ε ≤ δ ^ C / C →
    ∀ u v : Polynomial ℝ, u.natDegree ≤ 2 → v.natDegree ≤ 2 →
      ∀ L : ℕ, (C : ℝ) * (δ ^ C)⁻¹ ≤ L →
        ∀ Γ : Finset (ℕ × ℕ),
          (∀ p ∈ Γ, (L : ℝ) / 2 < p.1 ∧ (p.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < p.2 ∧ (p.2 : ℝ) ≤ L) →
          δ * (L : ℝ) ^ 2 ≤ Γ.card →
          (∀ p ∈ Γ, ‖((u.eval (p.1 : ℝ) + v.eval (p.2 : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε) →
          ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
            ‖(((q : ℝ) * u.coeff 2 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 ∧
            ‖(((q : ℝ) * v.coeff 2 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 ∧
            ‖(((q : ℝ) * u.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ∧
            ‖(((q : ℝ) * v.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ∧
            ‖(((q : ℝ) * (u.coeff 0 + v.coeff 0) : ℝ) : UnitAddCircle)‖
              ≤ C * (δ ^ C)⁻¹ * ε

theorem exists_vino2Spec : ∃ C : ℕ, Vino2Spec C := vinogradov_two_var_separate

/-- The two-variable Vinogradov constant may be taken at least one. -/
theorem exists_vino2Spec_pos : ∃ C : ℕ, 1 ≤ C ∧ Vino2Spec C := by
  obtain ⟨C, hC⟩ := exists_vino2Spec
  refine ⟨C, ?_, hC⟩
  by_contra hlt
  have hC0 : C = 0 := by omega
  subst hC0
  obtain ⟨q, hq0, hq, -⟩ := hC 1 0 one_pos le_rfl (by simp) 0 0 (by simp) (by simp) 0 (by simp) ∅
    (by simp) (by simp) (by simp)
  simp at hq
  omega

/-- Two-variable Vinogradov for `β⁰ ℓ + β¹ ℓ'`. -/
theorem vino2_lin {C : ℕ} (hV : Vino2Spec C) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : ε ≤ δ ^ C / C) {L : ℕ} (hL : (C : ℝ) * (δ ^ C)⁻¹ ≤ L) {Γ : Finset (ℕ × ℕ)}
    (hΓ : ∀ p ∈ Γ, (L : ℝ) / 2 < p.1 ∧ (p.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < p.2 ∧ (p.2 : ℝ) ≤ L)
    (hcard : δ * (L : ℝ) ^ 2 ≤ Γ.card) {β₀ β₁ : ℝ}
    (h : ∀ p ∈ Γ, ‖((β₀ * (p.1 : ℝ) + β₁ * (p.2 : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
      ‖(((Q : ℝ) * β₀ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / L ∧
      ‖(((Q : ℝ) * β₁ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / L := by
  obtain ⟨Q, hQ0, hQ, -, -, h1, h1', -⟩ := hV δ ε hδ hδ1 hε (Polynomial.C β₀ * Polynomial.X)
    (Polynomial.C β₁ * Polynomial.X) (by compute_degree!) (by compute_degree!) L hL Γ hΓ hcard
    (fun p hp => by simpa using h p hp)
  exact ⟨Q, hQ0, hQ, by simpa using h1, by simpa using h1'⟩

/-- Two-variable Vinogradov for `β⁰ ℓ² + β¹ ℓ'²`. -/
theorem vino2_quad {C : ℕ} (hV : Vino2Spec C) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : ε ≤ δ ^ C / C) {L : ℕ} (hL : (C : ℝ) * (δ ^ C)⁻¹ ≤ L) {Γ : Finset (ℕ × ℕ)}
    (hΓ : ∀ p ∈ Γ, (L : ℝ) / 2 < p.1 ∧ (p.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < p.2 ∧ (p.2 : ℝ) ≤ L)
    (hcard : δ * (L : ℝ) ^ 2 ≤ Γ.card) {β₀ β₁ : ℝ}
    (h : ∀ p ∈ Γ, ‖((β₀ * (p.1 : ℝ) ^ 2 + β₁ * (p.2 : ℝ) ^ 2 : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
      ‖(((Q : ℝ) * β₀ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 ∧
      ‖(((Q : ℝ) * β₁ : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / (L : ℝ) ^ 2 := by
  obtain ⟨Q, hQ0, hQ, h2, h2', -, -, -⟩ := hV δ ε hδ hδ1 hε (Polynomial.C β₀ * Polynomial.X ^ 2)
    (Polynomial.C β₁ * Polynomial.X ^ 2) (by compute_degree!) (by compute_degree!) L hL Γ hΓ hcard
    (fun p hp => by simpa using h p hp)
  exact ⟨Q, hQ0, hQ, by simpa using h2, by simpa using h2'⟩

/-- **Steps 2 and 3 for all the pivot functionals of the product.**  Let `Γ ⊆ (L/2, L]²` have
`|Γ| ≥ δ L²` and, for `(ℓ, ℓ') ∈ Γ`, let `E P R = (δ_{qℓ} X, δ_{qℓ'} X)` be data in the group of
`a.prod` with a common grid `(1/m) ℤ`, `P` killed by the pivot functionals.  Then there is
`Q ≤ V^{|Z₁| + |Z₂|}` (`V = C δ^{-C}`) such that for every pivot functional `θ = (θ⁰, θ¹)` the
numbers `Q q m θ⁰(x₁)`, `Q q m θ¹(x₁)` (resp. `Q q² m θ⁰(x₂)`, `Q q² m θ¹(x₂)` in layer two) are
within `Q V ε₁ / L` (resp. `Q V ε₂ / L²`) of integers. -/
theorem character_family₂ {C : ℕ} (hV : Vino2Spec C) (X : SymbolGroup a) (q m : ℕ)
    {δ M A Hθ ε₁ ε₂ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hHθ : 0 ≤ Hθ) (hM : 0 ≤ M) (hA : 0 < A)
    {L : ℕ} (hL : (C : ℝ) * (δ ^ C)⁻¹ ≤ L)
    (hε₁ : (m : ℝ) * (Fintype.card (ι₁ ⊕ ι₁) * (Hθ * (M / A))) ≤ ε₁) (hε₁' : ε₁ ≤ δ ^ C / C)
    (hε₂ : (m : ℝ) * (Fintype.card (ι₂ ⊕ ι₂) * (Hθ * (M / A ^ 2))) ≤ ε₂)
    (hε₂' : ε₂ ≤ δ ^ C / C) {Γ : Finset (ℕ × ℕ)}
    (hΓ : ∀ p ∈ Γ, (L : ℝ) / 2 < p.1 ∧ (p.1 : ℝ) ≤ L ∧ (L : ℝ) / 2 < p.2 ∧ (p.2 : ℝ) ≤ L)
    (hcard : δ * (L : ℝ) ^ 2 ≤ Γ.card) (Ef Pf Rf : ℕ × ℕ → SymbolGroup a.prod)
    (hprod : ∀ pr ∈ Γ, Ef pr * Pf pr * Rf pr =
      SymbolGroup.biDil ((q : ℝ) * pr.1) ((q : ℝ) * pr.2) X)
    (hE₁ : ∀ pr ∈ Γ, ∀ i, |(Ef pr).fst i| ≤ M / A)
    (hE₂ : ∀ pr ∈ Γ, ∀ k, |(Ef pr).snd k| ≤ M / A ^ 2)
    (hR₁ : ∀ pr ∈ Γ, ∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * (Rf pr).fst i)
    (hR₂ : ∀ pr ∈ Γ, ∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * (Rf pr).snd k)
    (Z₁ : Finset (ι₁ ⊕ ι₁)) (θ₁ : ι₁ ⊕ ι₁ → ι₁ ⊕ ι₁ → ℤ) (hθ₁ : ∀ j i, |(θ₁ j i : ℝ)| ≤ Hθ)
    (Z₂ : Finset (ι₂ ⊕ ι₂)) (θ₂ : ι₂ ⊕ ι₂ → ι₂ ⊕ ι₂ → ℤ) (hθ₂ : ∀ j i, |(θ₂ j i : ℝ)| ≤ Hθ)
    (hbr : ∀ j ∈ Z₂, ∀ i i', ∑ k, (θ₂ j k : ℚ) * a.prod.c i i' k = 0)
    (hP₁ : ∀ pr ∈ Γ, ∀ j ∈ Z₁, fnl (θ₁ j) (Pf pr).fst = 0)
    (hP₂ : ∀ pr ∈ Γ, ∀ j ∈ Z₂, fnl (θ₂ j) (Pf pr).snd = 0) :
    ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ ((C : ℝ) * (δ ^ C)⁻¹) ^ (Z₁.card + Z₂.card) ∧
      (∀ j ∈ Z₁,
        (∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) * m * fnl (fun i => θ₁ j (.inl i)) X.fst) - y| ≤
          Q * ((C : ℝ) * (δ ^ C)⁻¹ * ε₁ / L)) ∧
        (∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) * m * fnl (fun i => θ₁ j (.inr i)) X.fst) - y| ≤
          Q * ((C : ℝ) * (δ ^ C)⁻¹ * ε₁ / L))) ∧
      (∀ j ∈ Z₂,
        (∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inl i)) X.snd) - y| ≤
          Q * ((C : ℝ) * (δ ^ C)⁻¹ * ε₂ / (L : ℝ) ^ 2)) ∧
        (∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inr i)) X.snd) - y| ≤
          Q * ((C : ℝ) * (δ ^ C)⁻¹ * ε₂ / (L : ℝ) ^ 2))) := by
  classical
  have h1 : ∀ j, ∃ Qj : ℕ, j ∈ Z₁ → (0 < Qj ∧ (Qj : ℝ) ≤ (C : ℝ) * (δ ^ C)⁻¹ ∧
      ‖(((Qj : ℝ) * ((q : ℝ) * m * fnl (fun i => θ₁ j (.inl i)) X.fst) : ℝ) :
        UnitAddCircle)‖ ≤ (C : ℝ) * (δ ^ C)⁻¹ * ε₁ / L ∧
      ‖(((Qj : ℝ) * ((q : ℝ) * m * fnl (fun i => θ₁ j (.inr i)) X.fst) : ℝ) :
        UnitAddCircle)‖ ≤ (C : ℝ) * (δ ^ C)⁻¹ * ε₁ / L) := by
    intro j
    by_cases hj : j ∈ Z₁
    · obtain ⟨Qj, h0, hq, hn, hn'⟩ := vino2_lin hV hδ hδ1 hε₁' hL hΓ hcard
        (β₀ := (q : ℝ) * m * fnl (fun i => θ₁ j (.inl i)) X.fst)
        (β₁ := (q : ℝ) * m * fnl (fun i => θ₁ j (.inr i)) X.fst) (fun pr hpr => by
          have h := layer_one_gen (Ef pr) (Pf pr) (Rf pr) m (θ₁ j) hHθ (hθ₁ j) (hE₁ pr hpr)
            (hR₁ pr hpr) (hP₁ pr hpr j hj)
          rw [hprod pr hpr] at h
          have e : (m : ℝ) * fnl (θ₁ j) (SymbolGroup.biDil ((q : ℝ) * pr.1) ((q : ℝ) * pr.2)
              X).fst = ((q : ℝ) * m * fnl (fun i => θ₁ j (.inl i)) X.fst) * (pr.1 : ℝ) +
              ((q : ℝ) * m * fnl (fun i => θ₁ j (.inr i)) X.fst) * (pr.2 : ℝ) := by
            change (m : ℝ) * fnl (θ₁ j) (Sum.elim (((q : ℝ) * pr.1) • X.fst)
              (((q : ℝ) * pr.2) • X.fst)) = _
            rw [fnl_sumElim]
            ring
          rw [e] at h
          exact h.trans hε₁)
      exact ⟨Qj, fun _ => ⟨h0, hq, hn, hn'⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  have h2 : ∀ j, ∃ Qj : ℕ, j ∈ Z₂ → (0 < Qj ∧ (Qj : ℝ) ≤ (C : ℝ) * (δ ^ C)⁻¹ ∧
      ‖(((Qj : ℝ) * ((q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inl i)) X.snd) : ℝ) :
        UnitAddCircle)‖ ≤ (C : ℝ) * (δ ^ C)⁻¹ * ε₂ / (L : ℝ) ^ 2 ∧
      ‖(((Qj : ℝ) * ((q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inr i)) X.snd) : ℝ) :
        UnitAddCircle)‖ ≤ (C : ℝ) * (δ ^ C)⁻¹ * ε₂ / (L : ℝ) ^ 2) := by
    intro j
    by_cases hj : j ∈ Z₂
    · obtain ⟨Qj, h0, hq, hn, hn'⟩ := vino2_quad hV hδ hδ1 hε₂' hL hΓ hcard
        (β₀ := (q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inl i)) X.snd)
        (β₁ := (q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inr i)) X.snd) (fun pr hpr => by
          have h := layer_two_gen (Ef pr) (Pf pr) (Rf pr) m (θ₂ j) (hbr j hj) hHθ (hθ₂ j)
            (hE₂ pr hpr) (hR₂ pr hpr) (hP₂ pr hpr j hj)
          rw [hprod pr hpr] at h
          have e : (m : ℝ) * fnl (θ₂ j) (SymbolGroup.biDil ((q : ℝ) * pr.1) ((q : ℝ) * pr.2)
              X).snd = ((q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inl i)) X.snd) * (pr.1 : ℝ) ^ 2 +
              ((q : ℝ) ^ 2 * m * fnl (fun i => θ₂ j (.inr i)) X.snd) * (pr.2 : ℝ) ^ 2 := by
            change (m : ℝ) * fnl (θ₂ j) (Sum.elim ((((q : ℝ) * pr.1) ^ 2) • X.snd)
              ((((q : ℝ) * pr.2) ^ 2) • X.snd)) = _
            rw [fnl_sumElim]
            ring
          rw [e] at h
          exact h.trans hε₂)
      exact ⟨Qj, fun _ => ⟨h0, hq, hn, hn'⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose Q₁ hQ₁ using h1
  choose Q₂ hQ₂ using h2
  have hQpos : 0 < (∏ j ∈ Z₁, Q₁ j) * ∏ j ∈ Z₂, Q₂ j :=
    Nat.mul_pos (Finset.prod_pos fun j hj => (hQ₁ j hj).1)
      (Finset.prod_pos fun j hj => (hQ₂ j hj).1)
  have hV0 : (0 : ℝ) ≤ (C : ℝ) * (δ ^ C)⁻¹ := by positivity
  have hε₁0 : 0 ≤ ε₁ := le_trans (by positivity) hε₁
  have hε₂0 : 0 ≤ ε₂ := le_trans (by positivity) hε₂
  have hr₁ : 0 ≤ (C : ℝ) * (δ ^ C)⁻¹ * ε₁ / L :=
    div_nonneg (mul_nonneg hV0 hε₁0) (Nat.cast_nonneg L)
  have hr₂ : 0 ≤ (C : ℝ) * (δ ^ C)⁻¹ * ε₂ / (L : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg hV0 hε₂0) (by positivity)
  have hp1 : ∏ j ∈ Z₁, (Q₁ j : ℝ) ≤ ((C : ℝ) * (δ ^ C)⁻¹) ^ Z₁.card := by
    calc ∏ j ∈ Z₁, (Q₁ j : ℝ) ≤ ∏ _j ∈ Z₁, (C : ℝ) * (δ ^ C)⁻¹ :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun j hj => (hQ₁ j hj).2.1
      _ = ((C : ℝ) * (δ ^ C)⁻¹) ^ Z₁.card := Finset.prod_const _
  have hp2 : ∏ j ∈ Z₂, (Q₂ j : ℝ) ≤ ((C : ℝ) * (δ ^ C)⁻¹) ^ Z₂.card := by
    calc ∏ j ∈ Z₂, (Q₂ j : ℝ) ≤ ∏ _j ∈ Z₂, (C : ℝ) * (δ ^ C)⁻¹ :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun j hj => (hQ₂ j hj).2.1
      _ = ((C : ℝ) * (δ ^ C)⁻¹) ^ Z₂.card := Finset.prod_const _
  refine ⟨(∏ j ∈ Z₁, Q₁ j) * ∏ j ∈ Z₂, Q₂ j, hQpos, ?_, ?_, ?_⟩
  · push_cast
    calc (∏ j ∈ Z₁, (Q₁ j : ℝ)) * ∏ j ∈ Z₂, (Q₂ j : ℝ)
        ≤ ((C : ℝ) * (δ ^ C)⁻¹) ^ Z₁.card * ((C : ℝ) * (δ ^ C)⁻¹) ^ Z₂.card :=
          mul_le_mul hp1 hp2 (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
            (pow_nonneg hV0 _)
      _ = ((C : ℝ) * (δ ^ C)⁻¹) ^ (Z₁.card + Z₂.card) := (pow_add _ _ _).symm
  · intro j hj
    exact ⟨dist_of_dvd (hQ₁ j hj).1 (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hj) _) hr₁
      (hQ₁ j hj).2.2.1, dist_of_dvd (hQ₁ j hj).1
      (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hj) _) hr₁ (hQ₁ j hj).2.2.2⟩
  · intro j hj
    exact ⟨dist_of_dvd (hQ₂ j hj).1 (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hj) _) hr₂
      (hQ₂ j hj).2.2.1, dist_of_dvd (hQ₂ j hj).1
      (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hj) _) hr₂ (hQ₂ j hj).2.2.2⟩

end PrimeCarleson.Proof.Fplus31
