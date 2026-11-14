module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Datum
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Module

/-!
# Step 4 of the extrapolation step: the Cramer lift through the abelianization

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). Let `θ¹_j` (`j ∈ Z₁`) and `θ²_j` (`j ∈ Z₂`) be integer functionals
of the pivot form of `Pivot.lean` (`θ_j (e_{z j'}) = Δ δ_{j j'}`), with the `θ²_j` killing the
structure constants. If `N₁ θ¹_j(X₁)` and `N₂ θ²_j(X₂)` are within `τ₁` and `τ₂` of integers, then
`X = E P R` with `E` of sup norm at most `τ₁` (layer one) and `τ₂` (layer two), `R` in the grid
`(1 / (N₁ N₂ Δ₁ Δ₂)) ℤ`, and `P` killed by all the `θ_j` (`reconstruct`). The factors are
`E = Σ_j e_{z j} (N θ_j(X) - y_j) / (N Δ)`, `R = Σ_j e_{z j} y_j / (N Δ)` supported on the free
coordinates (where `θ_j` is `Δ` times the coordinate), and `P = E⁻¹ X R⁻¹`; the bracket terms of `P`
are killed because `θ²_j` kills `D`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

/-- The real extension `y ↦ Σ θ_i y_i` of an integer functional. -/
def fnl {ι : Type*} [Fintype ι] (θ : ι → ℤ) (y : ι → ℝ) : ℝ := ∑ i, (θ i : ℝ) * y i

section Fnl

variable {ι : Type*} [Fintype ι] (θ : ι → ℤ)

theorem fnl_add (y y' : ι → ℝ) : fnl θ (y + y') = fnl θ y + fnl θ y' := by
  simp [fnl, mul_add, Finset.sum_add_distrib]

theorem fnl_sub (y y' : ι → ℝ) : fnl θ (y - y') = fnl θ y - fnl θ y' := by
  simp [fnl, mul_sub, Finset.sum_sub_distrib]

theorem fnl_smul (t : ℝ) (y : ι → ℝ) : fnl θ (t • y) = t * fnl θ y := by
  simp only [fnl, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem fnl_zero : fnl θ (0 : ι → ℝ) = 0 := by simp [fnl]

theorem fnl_single [DecidableEq ι] (i₀ : ι) (v : ℝ) : fnl θ (Pi.single i₀ v) = θ i₀ * v := by
  simp [fnl, Pi.single_apply]

theorem fnl_sum {κ : Type*} (s : Finset κ) (f : κ → ι → ℝ) :
    fnl θ (∑ j ∈ s, f j) = ∑ j ∈ s, fnl θ (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fnl_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, fnl_add, ih, Finset.sum_insert hj]

end Fnl

section Comb

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : Finset ι} {Δ : ℕ} {θ : ι → ι → ℤ}
  {z : ι → ι}

/-- On a combination `Σ_j c_j e_{z j}` of the free coordinates, `θ_j` reads `Δ c_j`. -/
theorem fnl_comb (hθ : ∀ j ∈ Z, ∀ j' ∈ Z, θ j (z j') = if j = j' then (Δ : ℤ) else 0)
    (c : ι → ℝ) {j : ι} (hj : j ∈ Z) :
    fnl (θ j) (∑ j' ∈ Z, Pi.single (z j') (c j')) = Δ * c j := by
  rw [fnl_sum]
  simp only [fnl_single]
  rw [Finset.sum_eq_single_of_mem j hj]
  · simp [hθ j hj j hj]
  · intro j' hj' hne
    rw [hθ j hj j' hj']
    simp [Ne.symm hne]

omit [Fintype ι] in
/-- The map `j ↦ z j` is injective on `Z` when `Δ ≠ 0`. -/
theorem injOn_of_diag (hΔ : 0 < Δ)
    (hθ : ∀ j ∈ Z, ∀ j' ∈ Z, θ j (z j') = if j = j' then (Δ : ℤ) else 0) :
    Set.InjOn z Z := by
  intro j hj j' hj' h
  by_contra hne
  have h3 : θ j (z j') = θ j (z j) := by rw [h]
  rw [hθ j hj j' hj', hθ j hj j hj] at h3
  have h4 : (0 : ℤ) = Δ := by simpa [hne] using h3
  omega

omit [Fintype ι] in
/-- The coordinates of a combination of free coordinates are bounded by the coefficients. -/
theorem comb_apply_bound (hΔ : 0 < Δ)
    (hθ : ∀ j ∈ Z, ∀ j' ∈ Z, θ j (z j') = if j = j' then (Δ : ℤ) else 0)
    (c : ι → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (hc : ∀ j ∈ Z, |c j| ≤ τ) (i : ι) :
    |(∑ j ∈ Z, (Pi.single (z j) (c j) : ι → ℝ)) i| ≤ τ := by
  rw [Finset.sum_apply]
  by_cases h : ∃ j ∈ Z, z j = i
  · obtain ⟨j, hj, rfl⟩ := h
    rw [Finset.sum_eq_single_of_mem j hj]
    · simpa using hc j hj
    · intro j' hj' hne
      have : z j' ≠ z j := fun h' => hne (injOn_of_diag hΔ hθ hj' hj h')
      simp [this]
  · push Not at h
    rw [Finset.sum_eq_zero]
    · simpa using hτ
    · intro j hj
      simp [(h j hj).symm]

omit [Fintype ι] in
/-- A combination of free coordinates with coefficients in `(1/m) ℤ` lies in `(1/m) ℤ`. -/
theorem comb_apply_grid (c : ι → ℝ) (m : ℝ) (hc : ∀ j ∈ Z, ∃ k : ℤ, (k : ℝ) = m * c j) (i : ι) :
    ∃ k : ℤ, (k : ℝ) = m * (∑ j ∈ Z, (Pi.single (z j) (c j) : ι → ℝ)) i := by
  classical
  choose! k hk using hc
  refine ⟨∑ j ∈ Z, if z j = i then k j else 0, ?_⟩
  rw [Finset.sum_apply, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases h : z j = i
  · subst h
    simp [hk j hj]
  · simp [Ne.symm h, h]

end Comb

section Bracket

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {a : Step2Algebra ι₁ ι₂}

/-- A functional killing all structure constants kills the real bracket. -/
theorem fnl_br_zero (θ : ι₂ → ℤ) (h : ∀ i i', ∑ k, (θ k : ℚ) * a.c i i' k = 0)
    (u v : ι₁ → ℝ) : fnl θ (a.br u v) = 0 := by
  simp only [fnl, Step2Algebra.br_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i' _ => ?_
  have h1 : ∑ k, (θ k : ℝ) * (a.c i i' k : ℝ) = 0 := by
    have := congrArg (Rat.cast : ℚ → ℝ) (h i i')
    simpa using this
  calc ∑ k, (θ k : ℝ) * (u i * v i' * (a.c i i' k : ℝ))
      = (u i * v i') * ∑ k, (θ k : ℝ) * (a.c i i' k : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [h1, mul_zero]

end Bracket

section Reconstruct

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  {a : Step2Algebra ι₁ ι₂}

/-- **Step 4 (Cramer lift).**  See the module documentation. -/
theorem reconstruct (X : SymbolGroup a)
    (Z₁ : Finset ι₁) (Δ₁ : ℕ) (hΔ₁ : 0 < Δ₁) (θ₁ : ι₁ → ι₁ → ℤ) (z₁ : ι₁ → ι₁)
    (hθ₁ : ∀ j ∈ Z₁, ∀ j' ∈ Z₁, θ₁ j (z₁ j') = if j = j' then (Δ₁ : ℤ) else 0)
    (Z₂ : Finset ι₂) (Δ₂ : ℕ) (hΔ₂ : 0 < Δ₂) (θ₂ : ι₂ → ι₂ → ℤ) (z₂ : ι₂ → ι₂)
    (hθ₂ : ∀ j ∈ Z₂, ∀ j' ∈ Z₂, θ₂ j (z₂ j') = if j = j' then (Δ₂ : ℤ) else 0)
    (hbr : ∀ j ∈ Z₂, ∀ i i', ∑ k, (θ₂ j k : ℚ) * a.c i i' k = 0)
    (N₁ N₂ : ℕ) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) {τ₁ τ₂ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (y₁ : ι₁ → ℤ) (y₂ : ι₂ → ℤ)
    (h₁ : ∀ j ∈ Z₁, |(N₁ : ℝ) * fnl (θ₁ j) X.fst - y₁ j| ≤ τ₁)
    (h₂ : ∀ j ∈ Z₂, |(N₂ : ℝ) * fnl (θ₂ j) X.snd - y₂ j| ≤ τ₂) :
    ∃ E P R : SymbolGroup a, E * P * R = X ∧ (∀ i, |E.fst i| ≤ τ₁) ∧ (∀ k, |E.snd k| ≤ τ₂) ∧
      (∀ i, ∃ w : ℤ, (w : ℝ) = ((N₁ * N₂ * Δ₁ * Δ₂ : ℕ) : ℝ) * R.fst i) ∧
      (∀ k, ∃ w : ℤ, (w : ℝ) = ((N₁ * N₂ * Δ₁ * Δ₂ : ℕ) : ℝ) * R.snd k) ∧
      (∀ j ∈ Z₁, fnl (θ₁ j) P.fst = 0) ∧ (∀ j ∈ Z₂, fnl (θ₂ j) P.snd = 0) := by
  have hN₁' : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
  have hN₂' : (0 : ℝ) < N₂ := by exact_mod_cast hN₂
  have hΔ₁' : (0 : ℝ) < Δ₁ := by exact_mod_cast hΔ₁
  have hΔ₂' : (0 : ℝ) < Δ₂ := by exact_mod_cast hΔ₂
  let ev₁ : ι₁ → ℝ := fun j => ((N₁ : ℝ) * fnl (θ₁ j) X.fst - y₁ j) / (N₁ * Δ₁)
  let rv₁ : ι₁ → ℝ := fun j => (y₁ j : ℝ) / (N₁ * Δ₁)
  let ev₂ : ι₂ → ℝ := fun j => ((N₂ : ℝ) * fnl (θ₂ j) X.snd - y₂ j) / (N₂ * Δ₂)
  let rv₂ : ι₂ → ℝ := fun j => (y₂ j : ℝ) / (N₂ * Δ₂)
  let E : SymbolGroup a := ⟨∑ j ∈ Z₁, Pi.single (z₁ j) (ev₁ j), ∑ j ∈ Z₂, Pi.single (z₂ j) (ev₂ j)⟩
  let R : SymbolGroup a := ⟨∑ j ∈ Z₁, Pi.single (z₁ j) (rv₁ j), ∑ j ∈ Z₂, Pi.single (z₂ j) (rv₂ j)⟩
  refine ⟨E, E⁻¹ * X * R⁻¹, R, by group, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine comb_apply_bound hΔ₁ hθ₁ ev₁ hτ₁ (fun j hj => ?_) i
    simp only [ev₁]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N₁ * Δ₁), div_le_iff₀ (by positivity)]
    refine (h₁ j hj).trans ?_
    have : (1 : ℝ) ≤ N₁ * Δ₁ := by
      have h1 : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
      have h2 : (1 : ℝ) ≤ Δ₁ := by exact_mod_cast hΔ₁
      nlinarith
    nlinarith
  · intro k
    refine comb_apply_bound hΔ₂ hθ₂ ev₂ hτ₂ (fun j hj => ?_) k
    simp only [ev₂]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N₂ * Δ₂), div_le_iff₀ (by positivity)]
    refine (h₂ j hj).trans ?_
    have : (1 : ℝ) ≤ N₂ * Δ₂ := by
      have h1 : (1 : ℝ) ≤ N₂ := by exact_mod_cast hN₂
      have h2 : (1 : ℝ) ≤ Δ₂ := by exact_mod_cast hΔ₂
      nlinarith
    nlinarith
  · intro i
    refine comb_apply_grid rv₁ _ (fun j _ => ⟨y₁ j * (N₂ * Δ₂ : ℕ), ?_⟩) i
    simp only [rv₁]
    push_cast
    field_simp
  · intro k
    refine comb_apply_grid rv₂ _ (fun j _ => ⟨y₂ j * (N₁ * Δ₁ : ℕ), ?_⟩) k
    simp only [rv₂]
    push_cast
    field_simp
  · intro j hj
    have hP : (E⁻¹ * X * R⁻¹).fst = X.fst - E.fst - R.fst := by
      simp only [SymbolGroup.mul_fst, SymbolGroup.inv_fst]
      abel
    rw [hP, fnl_sub, fnl_sub]
    have e1 : fnl (θ₁ j) E.fst = Δ₁ * ev₁ j := fnl_comb hθ₁ ev₁ hj
    have e2 : fnl (θ₁ j) R.fst = Δ₁ * rv₁ j := fnl_comb hθ₁ rv₁ hj
    rw [e1, e2]
    simp only [ev₁, rv₁]
    field_simp
    ring
  · intro j hj
    have hP : (E⁻¹ * X * R⁻¹).snd = X.snd - E.snd - R.snd +
        (-(1 / 2 : ℝ) • a.br E.fst X.fst - (1 / 2 : ℝ) • a.br (X.fst - E.fst) R.fst) := by
      simp only [SymbolGroup.mul_snd, SymbolGroup.mul_fst, SymbolGroup.inv_fst,
        SymbolGroup.inv_snd, Step2Algebra.br_neg_left, Step2Algebra.br_neg_right, smul_neg,
        neg_add_eq_sub]
      module
    have hb := fnl_br_zero (a := a) (θ₂ j) (hbr j hj)
    rw [hP, fnl_add, fnl_sub, fnl_sub, fnl_sub, fnl_smul, fnl_smul, hb, hb]
    have e1 : fnl (θ₂ j) E.snd = Δ₂ * ev₂ j := fnl_comb hθ₂ ev₂ hj
    have e2 : fnl (θ₂ j) R.snd = Δ₂ * rv₂ j := fnl_comb hθ₂ rv₂ hj
    rw [e1, e2]
    simp only [ev₂, rv₂]
    field_simp
    ring

end Reconstruct

end PrimeCarleson.Proof.Fplus31
