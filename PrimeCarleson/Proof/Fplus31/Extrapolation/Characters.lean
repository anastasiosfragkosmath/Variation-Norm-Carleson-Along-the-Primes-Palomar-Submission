module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Reconstruct
public import PrimeCarleson.Proof.Fplus31.Vinogradov.OneVariable
public import Mathlib.Tactic.ComputeDegree

/-!
# Extrapolation, steps 2 and 3: the character identity and the many-dilates Vinogradov lemma

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1).

* `layer_one_dist` and `layer_two_dist` (Step 2): from a datum `E P R = δ_{qℓ} X` and an integer
  functional `θ` killing `P` (and, in layer two, the structure constants),
  `‖(q m θ(x₁)) ℓ‖_{ℝ/ℤ} ≤ m n H M / A` and `‖(q² m θ(x₂)) ℓ²‖_{ℝ/ℤ} ≤ m n H M / A²`. The
  functionals `θ₁ ∘ pr₁` and `θ₂ ∘ pr₂` are used separately.
* `VinoSpec`, `vino_lin`, `vino_quad` (Step 3): the Vinogradov lemma of
  `Vinogradov/OneVariable.lean` for the polynomials `β ℓ` and `β ℓ²`.
* `character_family`: for all the pivot functionals of both layers at once, a common
  denominator `Q ≤ V^{|Z₁| + |Z₂|}` (`V = C δ^{-C}`) with `‖Q q m θ¹_j(x₁)‖` and
  `‖Q q² m θ²_j(x₂)‖` small, as distances to integers.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The bound on a functional of sup norm at most `H` applied to a vector of sup norm at most
`B`. -/
theorem abs_fnl_le {ι : Type*} [Fintype ι] (θ : ι → ℤ) {H B : ℝ} (hH : 0 ≤ H)
    (hθ : ∀ i, |(θ i : ℝ)| ≤ H) (y : ι → ℝ) (hy : ∀ i, |y i| ≤ B) :
    |fnl θ y| ≤ Fintype.card ι * (H * B) := by
  calc |fnl θ y| ≤ ∑ i, |(θ i : ℝ) * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, H * B := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hθ i) (hy i) (abs_nonneg _) hH
    _ = Fintype.card ι * (H * B) := by simp

/-- The distance to the nearest integer is at most the absolute value. -/
theorem norm_coe_le_abs (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  simpa using norm_coe_le_abs_sub x 0

variable {ι₁ ι₂ : Type*} [Fintype ι₁] {a : Step2Algebra ι₁ ι₂}

/-- **Step 2, layer one.**  `‖(q m θ(x₁)) ℓ‖_{ℝ/ℤ} ≤ m n H M / A`. -/
theorem layer_one_dist (X : SymbolGroup a) (q m ℓ : ℕ) (E P R : SymbolGroup a)
    (hprod : E * P * R = SymbolGroup.dil ((q : ℝ) * ℓ) X) (θ : ι₁ → ℤ) {H M A : ℝ}
    (hH : 0 ≤ H) (hθ : ∀ i, |(θ i : ℝ)| ≤ H) (hE : ∀ i, |E.fst i| ≤ M / A)
    (hR : ∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.fst i) (hP : fnl θ P.fst = 0) :
    ‖((((q : ℝ) * m * fnl θ X.fst) * ℓ : ℝ) : UnitAddCircle)‖ ≤
      m * (Fintype.card ι₁ * (H * (M / A))) := by
  have h1 := congrArg SymbolGroup.fst hprod
  rw [SymbolGroup.mul₃_fst, SymbolGroup.dil_fst] at h1
  have h2 : fnl θ E.fst + fnl θ P.fst + fnl θ R.fst = ((q : ℝ) * ℓ) * fnl θ X.fst := by
    rw [← fnl_add, ← fnl_add, h1, fnl_smul]
  rw [hP, add_zero] at h2
  choose k hk using hR
  have hK : (m : ℝ) * fnl θ R.fst = ((∑ i, θ i * k i : ℤ) : ℝ) := by
    simp only [fnl, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk i]
    ring
  have hx : ((q : ℝ) * m * fnl θ X.fst) * ℓ = m * fnl θ E.fst + ((∑ i, θ i * k i : ℤ) : ℝ) := by
    rw [← hK]
    linear_combination (-(m : ℝ)) * h2
  rw [hx, norm_coe_add_intCast]
  refine (norm_coe_le_abs _).trans ?_
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  exact mul_le_mul_of_nonneg_left (abs_fnl_le θ hH hθ E.fst hE) (Nat.cast_nonneg m)

/-- **Step 2, layer two.**  `‖(q² m θ(x₂)) ℓ²‖_{ℝ/ℤ} ≤ m n H M / A²` when `θ` kills `P` and the
structure constants. -/
theorem layer_two_dist [Fintype ι₂] (X : SymbolGroup a) (q m ℓ : ℕ) (E P R : SymbolGroup a)
    (hprod : E * P * R = SymbolGroup.dil ((q : ℝ) * ℓ) X) (θ : ι₂ → ℤ) {H M A : ℝ}
    (hbr : ∀ i i', ∑ k, (θ k : ℚ) * a.c i i' k = 0)
    (hH : 0 ≤ H) (hθ : ∀ k, |(θ k : ℝ)| ≤ H) (hE : ∀ k, |E.snd k| ≤ M / A ^ 2)
    (hR : ∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.snd k) (hP : fnl θ P.snd = 0) :
    ‖((((q : ℝ) ^ 2 * m * fnl θ X.snd) * (ℓ : ℝ) ^ 2 : ℝ) : UnitAddCircle)‖ ≤
      m * (Fintype.card ι₂ * (H * (M / A ^ 2))) := by
  have h1 := congrArg SymbolGroup.snd hprod
  rw [SymbolGroup.mul₃_snd, SymbolGroup.dil_snd] at h1
  have hb := fnl_br_zero (a := a) θ hbr
  have h2 : fnl θ E.snd + fnl θ P.snd + fnl θ R.snd =
      (((q : ℝ) * ℓ) ^ 2) * fnl θ X.snd := by
    have h3 := congrArg (fnl θ) h1
    rw [fnl_add, fnl_add, fnl_add, fnl_smul, fnl_smul, fnl_add, fnl_add, hb, hb, hb] at h3
    linarith
  rw [hP, add_zero] at h2
  choose k hk using hR
  have hK : (m : ℝ) * fnl θ R.snd = ((∑ i, θ i * k i : ℤ) : ℝ) := by
    simp only [fnl, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk i]
    ring
  have hx : ((q : ℝ) ^ 2 * m * fnl θ X.snd) * (ℓ : ℝ) ^ 2 =
      m * fnl θ E.snd + ((∑ i, θ i * k i : ℤ) : ℝ) := by
    rw [← hK]
    linear_combination (-(m : ℝ)) * h2
  rw [hx, norm_coe_add_intCast]
  refine (norm_coe_le_abs _).trans ?_
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  exact mul_le_mul_of_nonneg_left (abs_fnl_le θ hH hθ E.snd hE) (Nat.cast_nonneg m)

/-- The statement of the many-dilates Vinogradov lemma for polynomials of degree at most two
(`vinogradov_poly_deg_le_two`) with the absolute constant `C` fixed. -/
def VinoSpec (C : ℕ) : Prop :=
  ∀ (δ ε : ℝ), 0 < δ → δ ≤ 1 → ε ≤ δ ^ C / C →
    ∀ P : Polynomial ℝ, P.natDegree ≤ 2 → ∀ L : ℕ, (C : ℝ) * (δ ^ C)⁻¹ ≤ L →
      ∀ Λ : Finset ℕ, (∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) → δ * L ≤ Λ.card →
        (∀ ℓ ∈ Λ, ‖((P.eval (ℓ : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε) →
        ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
          ‖(((q : ℝ) * P.coeff 2 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / L ^ 2 ∧
          ‖(((q : ℝ) * P.coeff 1 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / L ∧
          ‖(((q : ℝ) * P.coeff 0 : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε

theorem exists_vinoSpec : ∃ C : ℕ, VinoSpec C := vinogradov_poly_deg_le_two

/-- Vinogradov for the linear polynomial `β ℓ`. -/
theorem vino_lin {C : ℕ} (hV : VinoSpec C) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : ε ≤ δ ^ C / C) {L : ℕ} (hL : (C : ℝ) * (δ ^ C)⁻¹ ≤ L) {Λ : Finset ℕ}
    (hΛ : ∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) (hcard : δ * L ≤ Λ.card) {β : ℝ}
    (h : ∀ ℓ ∈ Λ, ‖((β * ℓ : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
      ‖(((Q : ℝ) * β : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / L := by
  obtain ⟨Q, hQ0, hQ, -, h1, -⟩ := hV δ ε hδ hδ1 hε (Polynomial.C β * Polynomial.X)
    (by compute_degree!) L hL Λ hΛ hcard (fun ℓ hℓ => by simpa using h ℓ hℓ)
  exact ⟨Q, hQ0, hQ, by simpa using h1⟩

/-- Vinogradov for the quadratic monomial `β ℓ²`. -/
theorem vino_quad {C : ℕ} (hV : VinoSpec C) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : ε ≤ δ ^ C / C) {L : ℕ} (hL : (C : ℝ) * (δ ^ C)⁻¹ ≤ L) {Λ : Finset ℕ}
    (hΛ : ∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) (hcard : δ * L ≤ Λ.card) {β : ℝ}
    (h : ∀ ℓ ∈ Λ, ‖((β * (ℓ : ℝ) ^ 2 : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ C * (δ ^ C)⁻¹ ∧
      ‖(((Q : ℝ) * β : ℝ) : UnitAddCircle)‖ ≤ C * (δ ^ C)⁻¹ * ε / L ^ 2 := by
  obtain ⟨Q, hQ0, hQ, h2, -, -⟩ := hV δ ε hδ hδ1 hε (Polynomial.C β * Polynomial.X ^ 2)
    (by compute_degree!) L hL Λ hΛ hcard (fun ℓ hℓ => by simpa using h ℓ hℓ)
  exact ⟨Q, hQ0, hQ, by simpa using h2⟩

/-- If `Q₁ β` is within `r` of an integer and `Q₁ ∣ Q`, then `Q β` is within `Q r` of an
integer. -/
theorem dist_of_dvd {Q Q₁ : ℕ} (hQ₁ : 0 < Q₁) (hd : Q₁ ∣ Q) {β r : ℝ} (hr : 0 ≤ r)
    (h : ‖(((Q₁ : ℝ) * β : ℝ) : UnitAddCircle)‖ ≤ r) : ∃ y : ℤ, |(Q : ℝ) * β - y| ≤ Q * r := by
  obtain ⟨Q', hQ'⟩ := hd
  have hQ'le : (Q' : ℝ) ≤ Q := by
    have : Q' ≤ Q := by
      rw [hQ']
      exact Nat.le_mul_of_pos_left Q' hQ₁
    exact_mod_cast this
  have heq : (Q : ℝ) * β = (Q' : ℝ) * ((Q₁ : ℝ) * β) := by
    rw [hQ']
    push_cast
    ring
  have hn : ‖(((Q : ℝ) * β : ℝ) : UnitAddCircle)‖ ≤ Q' * r := by
    rw [heq]
    exact (norm_natCast_mul_coe_le Q' _).trans
      (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
  obtain ⟨y, hy⟩ :=
    exists_abs_sub_le_of_norm_coe_le (hn.trans (mul_le_mul_of_nonneg_right hQ'le hr))
  exact ⟨y, hy⟩

/-- **Steps 2 and 3 for all the functionals.**  Let `Λ ⊆ (L/2, L]` have `|Λ| ≥ δ L` and, for
`ℓ ∈ Λ`, let `E P R = δ_{qℓ} X` be data with a common grid `(1/m) ℤ`, `P` killed by the pivot
functionals `θ¹_j` (`j ∈ Z₁`, layer one) and `θ²_j` (`j ∈ Z₂`, layer two, killing the structure
constants).  If `L ≥ C δ^{-C}` and the errors `ε₁`, `ε₂` bounding `m n H M / A` and
`m n H M / A²` are at most `δ^C / C`, then there is a positive integer `Q ≤ V^{|Z₁| + |Z₂|}`,
`V = C δ^{-C}`, with `Q q m θ¹_j(x₁)` within `Q V ε₁ / L` and `Q q² m θ²_j(x₂)` within
`Q V ε₂ / L²` of integers. -/
theorem character_family [Fintype ι₂] {C : ℕ} (hV : VinoSpec C) (X : SymbolGroup a) (q m : ℕ)
    {δ M A Hθ ε₁ ε₂ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hHθ : 0 ≤ Hθ) (hM : 0 ≤ M) (hA : 0 < A)
    {L : ℕ} (hL : (C : ℝ) * (δ ^ C)⁻¹ ≤ L)
    (hε₁ : (m : ℝ) * (Fintype.card ι₁ * (Hθ * (M / A))) ≤ ε₁) (hε₁' : ε₁ ≤ δ ^ C / C)
    (hε₂ : (m : ℝ) * (Fintype.card ι₂ * (Hθ * (M / A ^ 2))) ≤ ε₂) (hε₂' : ε₂ ≤ δ ^ C / C)
    {Λ : Finset ℕ} (hΛ : ∀ ℓ ∈ Λ, (L : ℝ) / 2 < ℓ ∧ (ℓ : ℝ) ≤ L) (hcard : δ * L ≤ Λ.card)
    (Ef Pf Rf : ℕ → SymbolGroup a)
    (hprod : ∀ ℓ ∈ Λ, Ef ℓ * Pf ℓ * Rf ℓ = SymbolGroup.dil ((q : ℝ) * ℓ) X)
    (hE₁ : ∀ ℓ ∈ Λ, ∀ i, |(Ef ℓ).fst i| ≤ M / A)
    (hE₂ : ∀ ℓ ∈ Λ, ∀ k, |(Ef ℓ).snd k| ≤ M / A ^ 2)
    (hR₁ : ∀ ℓ ∈ Λ, ∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * (Rf ℓ).fst i)
    (hR₂ : ∀ ℓ ∈ Λ, ∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * (Rf ℓ).snd k)
    (Z₁ : Finset ι₁) (θ₁ : ι₁ → ι₁ → ℤ) (hθ₁ : ∀ j i, |(θ₁ j i : ℝ)| ≤ Hθ)
    (Z₂ : Finset ι₂) (θ₂ : ι₂ → ι₂ → ℤ) (hθ₂ : ∀ j i, |(θ₂ j i : ℝ)| ≤ Hθ)
    (hbr : ∀ j ∈ Z₂, ∀ i i', ∑ k, (θ₂ j k : ℚ) * a.c i i' k = 0)
    (hP₁ : ∀ ℓ ∈ Λ, ∀ j ∈ Z₁, fnl (θ₁ j) (Pf ℓ).fst = 0)
    (hP₂ : ∀ ℓ ∈ Λ, ∀ j ∈ Z₂, fnl (θ₂ j) (Pf ℓ).snd = 0) :
    ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ ((C : ℝ) * (δ ^ C)⁻¹) ^ (Z₁.card + Z₂.card) ∧
      (∀ j ∈ Z₁, ∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) * m * fnl (θ₁ j) X.fst) - y| ≤
        Q * ((C : ℝ) * (δ ^ C)⁻¹ * ε₁ / L)) ∧
      (∀ j ∈ Z₂, ∃ y : ℤ, |(Q : ℝ) * ((q : ℝ) ^ 2 * m * fnl (θ₂ j) X.snd) - y| ≤
        Q * ((C : ℝ) * (δ ^ C)⁻¹ * ε₂ / (L : ℝ) ^ 2)) := by
  classical
  have h1 : ∀ j, ∃ Qj : ℕ, j ∈ Z₁ → (0 < Qj ∧ (Qj : ℝ) ≤ (C : ℝ) * (δ ^ C)⁻¹ ∧
      ‖(((Qj : ℝ) * ((q : ℝ) * m * fnl (θ₁ j) X.fst) : ℝ) : UnitAddCircle)‖ ≤
        (C : ℝ) * (δ ^ C)⁻¹ * ε₁ / L) := by
    intro j
    by_cases hj : j ∈ Z₁
    · obtain ⟨Qj, h0, hq, hn⟩ := vino_lin hV hδ hδ1 hε₁' hL hΛ hcard
        (β := (q : ℝ) * m * fnl (θ₁ j) X.fst) (fun ℓ hℓ => (layer_one_dist X q m ℓ (Ef ℓ)
          (Pf ℓ) (Rf ℓ) (hprod ℓ hℓ) (θ₁ j) hHθ (hθ₁ j) (hE₁ ℓ hℓ) (hR₁ ℓ hℓ)
          (hP₁ ℓ hℓ j hj)).trans hε₁)
      exact ⟨Qj, fun _ => ⟨h0, hq, hn⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  have h2 : ∀ j, ∃ Qj : ℕ, j ∈ Z₂ → (0 < Qj ∧ (Qj : ℝ) ≤ (C : ℝ) * (δ ^ C)⁻¹ ∧
      ‖(((Qj : ℝ) * ((q : ℝ) ^ 2 * m * fnl (θ₂ j) X.snd) : ℝ) : UnitAddCircle)‖ ≤
        (C : ℝ) * (δ ^ C)⁻¹ * ε₂ / (L : ℝ) ^ 2) := by
    intro j
    by_cases hj : j ∈ Z₂
    · obtain ⟨Qj, h0, hq, hn⟩ := vino_quad hV hδ hδ1 hε₂' hL hΛ hcard
        (β := (q : ℝ) ^ 2 * m * fnl (θ₂ j) X.snd) (fun ℓ hℓ => (layer_two_dist X q m ℓ (Ef ℓ)
          (Pf ℓ) (Rf ℓ) (hprod ℓ hℓ) (θ₂ j) (hbr j hj) hHθ (hθ₂ j) (hE₂ ℓ hℓ) (hR₂ ℓ hℓ)
          (hP₂ ℓ hℓ j hj)).trans hε₂)
      exact ⟨Qj, fun _ => ⟨h0, hq, hn⟩⟩
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
    exact dist_of_dvd (hQ₁ j hj).1 (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hj) _) hr₁
      (hQ₁ j hj).2.2
  · intro j hj
    exact dist_of_dvd (hQ₂ j hj).1 (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hj) _) hr₂
      (hQ₂ j hj).2.2

end PrimeCarleson.Proof.Fplus31
