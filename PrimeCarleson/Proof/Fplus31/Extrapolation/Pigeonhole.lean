module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Height
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.Pi

/-!
# Step 1 of the extrapolation step: the pigeonhole over the data of the dilates

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). The pair `(W_ℓ, m_ℓ)` of the datum of `δ_{qℓ} X` is determined by a
family `v : Fin d → g` of `d = dim g` vectors of coordinate log-height at most `p` and a grid size
`m ≤ e^p`; there are at most `e^{5 p³}` such pairs when `d ≤ p` and `p ≥ 1` (a rational of
log-height at most `p` has at most `3 e^{2p}` possibilities). `exists_common_class`: among more than
`e^{5 p³} b` values of `ℓ` some `b` share the pair.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- The vectors of `g = g₁ × g₂` with all coordinates in `ratBall N`. -/
def grBall (ι₁ ι₂ : Type*) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (N : ℕ) :
    Finset ((ι₁ → ℚ) × (ι₂ → ℚ)) :=
  Fintype.piFinset (fun _ : ι₁ => ratBall N) ×ˢ Fintype.piFinset (fun _ : ι₂ => ratBall N)

/-- The classes `(v, m)`: families of `D` vectors with coordinates in `ratBall N` and a grid size
`1 ≤ m ≤ N`. -/
def classBall (ι₁ ι₂ : Type*) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (D N : ℕ) :
    Finset ((Fin D → (ι₁ → ℚ) × (ι₂ → ℚ)) × ℕ) :=
  Fintype.piFinset (fun _ : Fin D => grBall ι₁ ι₂ N) ×ˢ Finset.Icc 1 N

theorem card_classBall (D N : ℕ) :
    (classBall ι₁ ι₂ D N).card =
      (ratBall N).card ^ ((Fintype.card ι₁ + Fintype.card ι₂) * D) * N := by
  simp only [classBall, grBall, Finset.card_product, Fintype.card_piFinset, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Nat.card_Icc, Nat.add_sub_cancel]
  ring

theorem card_ratBall_le_exp {p : ℝ} (hp : 1 ≤ p) :
    ((ratBall ⌊Real.exp p⌋₊).card : ℝ) ≤ Real.exp (4 * p) := by
  have h1 : (1 : ℝ) ≤ Real.exp p := Real.one_le_exp (by linarith)
  have hN1 : 1 ≤ ⌊Real.exp p⌋₊ := Nat.le_floor (by simpa using h1)
  have hNe : ((⌊Real.exp p⌋₊ : ℕ) : ℝ) ≤ Real.exp p := Nat.floor_le (Real.exp_nonneg _)
  have hN1' : (1 : ℝ) ≤ ⌊Real.exp p⌋₊ := by exact_mod_cast hN1
  have hcard : ((ratBall ⌊Real.exp p⌋₊).card : ℝ) ≤
      (2 * (⌊Real.exp p⌋₊ : ℝ) + 1) * ⌊Real.exp p⌋₊ := by
    exact_mod_cast card_ratBall_le ⌊Real.exp p⌋₊
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc ((ratBall ⌊Real.exp p⌋₊).card : ℝ)
      ≤ (2 * (⌊Real.exp p⌋₊ : ℝ) + 1) * ⌊Real.exp p⌋₊ := hcard
    _ ≤ (3 * ⌊Real.exp p⌋₊) * ⌊Real.exp p⌋₊ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ ≤ (Real.exp 2 * Real.exp p) * Real.exp p := by
        have : (3 : ℝ) * ⌊Real.exp p⌋₊ ≤ Real.exp 2 * Real.exp p :=
          mul_le_mul h3 hNe (by positivity) (Real.exp_nonneg _)
        exact mul_le_mul this hNe (by positivity) (by positivity)
    _ = Real.exp (2 + p + p) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (4 * p) := Real.exp_le_exp.mpr (by linarith)

/-- There are at most `e^{5 p³}` classes `(v, m)` when `d ≤ p` and `1 ≤ p`. -/
theorem card_classBall_le {p : ℝ} (hp : 1 ≤ p)
    (hd : ((Fintype.card ι₁ + Fintype.card ι₂ : ℕ) : ℝ) ≤ p) :
    ((classBall ι₁ ι₂ (Fintype.card ι₁ + Fintype.card ι₂) ⌊Real.exp p⌋₊).card : ℝ) ≤
      Real.exp (5 * p ^ 3) := by
  set D : ℕ := Fintype.card ι₁ + Fintype.card ι₂ with hD
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  rw [card_classBall]
  push_cast
  have hNe : ((⌊Real.exp p⌋₊ : ℕ) : ℝ) ≤ Real.exp p := Nat.floor_le (Real.exp_nonneg _)
  have hb := card_ratBall_le_exp hp
  calc (((ratBall ⌊Real.exp p⌋₊).card : ℝ)) ^ (D * D) * ⌊Real.exp p⌋₊
      ≤ (Real.exp (4 * p)) ^ (D * D) * Real.exp p := by
        apply mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hb _) hNe (Nat.cast_nonneg _)
          (by positivity)
    _ = Real.exp (4 * p * (D * D) + p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (5 * p ^ 3) := by
        apply Real.exp_le_exp.mpr
        have h1 : (D : ℝ) * D ≤ p * p := mul_le_mul hd hd hD0 (by linarith)
        have h2 : p ≤ p ^ 3 := by nlinarith [sq_nonneg p, sq_nonneg (p - 1)]
        nlinarith

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- **The pigeonhole of Step 1** (for an arbitrary finite index set `Λ` of dilation parameters).
If `ℓ ↦ (v ℓ, m ℓ)` takes values in the classes for all `ℓ ∈ Λ`, and `e^{5 p³} b ≤ |Λ|`, then
some class is taken on at least `b` values of `ℓ`. -/
theorem exists_common_class {α : Type*} {p : ℝ} (hp : 1 ≤ p)
    (hd : ((Fintype.card ι₁ + Fintype.card ι₂ : ℕ) : ℝ) ≤ p) {Λ : Finset α}
    (v : α → Fin (Fintype.card ι₁ + Fintype.card ι₂) → (ι₁ → ℚ) × (ι₂ → ℚ)) (mm : α → ℕ)
    (hv : ∀ ℓ ∈ Λ, ∀ r, (∀ i, ratLogHeight ((v ℓ r).1 i) ≤ p) ∧
      ∀ k, ratLogHeight ((v ℓ r).2 k) ≤ p)
    (hm : ∀ ℓ ∈ Λ, 0 < mm ℓ ∧ (mm ℓ : ℝ) ≤ Real.exp p) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : Real.exp (5 * p ^ 3) * b ≤ Λ.card) :
    ∃ Λ₁ ⊆ Λ, b ≤ Λ₁.card ∧ ∃ v₀ m₀, ∀ ℓ ∈ Λ₁, v ℓ = v₀ ∧ mm ℓ = m₀ := by
  classical
  have hmaps : ∀ ℓ ∈ Λ, (v ℓ, mm ℓ) ∈
      classBall ι₁ ι₂ (Fintype.card ι₁ + Fintype.card ι₂) ⌊Real.exp p⌋₊ := by
    intro ℓ hℓ
    simp only [classBall, grBall, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨fun r => ⟨fun i => mem_ratBall_of_ratLogHeight_le ((hv ℓ hℓ r).1 i),
      fun k => mem_ratBall_of_ratLogHeight_le ((hv ℓ hℓ r).2 k)⟩, (hm ℓ hℓ).1,
      Nat.le_floor (hm ℓ hℓ).2⟩
  have hne : (classBall ι₁ ι₂ (Fintype.card ι₁ + Fintype.card ι₂) ⌊Real.exp p⌋₊).Nonempty := by
    rw [← Finset.card_pos, card_classBall]
    have hN1 : 1 ≤ ⌊Real.exp p⌋₊ :=
      Nat.le_floor (by simpa using Real.one_le_exp (by linarith : (0 : ℝ) ≤ p))
    have hr : 0 < (ratBall ⌊Real.exp p⌋₊).card := by
      refine Finset.card_pos.mpr ⟨1, mem_ratBall ?_ ?_⟩ <;> simpa using hN1
    positivity
  have hcard : (classBall ι₁ ι₂ (Fintype.card ι₁ + Fintype.card ι₂) ⌊Real.exp p⌋₊).card • b ≤
      (Λ.card : ℝ) := by
    rw [nsmul_eq_mul]
    have h1 := card_classBall_le (ι₁ := ι₁) (ι₂ := ι₂) hp hd
    exact (mul_le_mul_of_nonneg_right h1 hb0).trans hb
  obtain ⟨y, hy, hfib⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (f := fun ℓ => (v ℓ, mm ℓ)) hmaps hne hcard
  refine ⟨Λ.filter fun ℓ => (v ℓ, mm ℓ) = y, Finset.filter_subset _ _, hfib, y.1, y.2, ?_⟩
  intro ℓ hℓ
  have := (Finset.mem_filter.mp hℓ).2
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

end PrimeCarleson.Proof.Fplus31
