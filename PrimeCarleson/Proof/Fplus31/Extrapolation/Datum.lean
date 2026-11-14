module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Height
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity

/-!
# Graded subalgebras and data (the extrapolation step)

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). The objects of the abstract statement over the graded step-two Lie
algebra `(g₁, g₂, β)` of `Model.lean`:

* `GradedSubalg a`: a graded `ℚ`-subalgebra `W = W₁ ⊕ W₂` of `g`, a `ℚ`-submodule of
  `g₁ × g₂` that is stable under the two projections and under the bracket;
* `derived a = D = β(g₁, g₁) = [g, g]` and `GradedSubalg.plusDerived W = W + D` (the subalgebra `K`,
  with `K₁ = W₁` and `K₂ = W₂ + D`);
* `realSpan W`: the real span `W_ℝ` of `W` (the Lie algebra of the group `exp (W_ℝ)`);
* `GradedSubalg.Gen W p`: `W` is spanned by `d = dim g` vectors of coordinate log-height at most `p`
  (the clause `v`, `hh` of the vendored library's `ControlledSymbolFactorization`);
* `Datum p W A M m Y`: the datum `(W; A, M, m)` for `Y` in the group `SymbolGroup a`: `Y = E P R`
  with `E` slow at scale `A` with constant `M` (`|e₁| ≤ M / A`, `|e₂| ≤ M / A²`), `R` in the grid
  `(1/m) ℤ` and `P ∈ exp (W_ℝ)`;
* `Datum.of_dil`: the undilation of Step 0.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section Real

variable {ι₁ ι₂ : Type*}

/-- The cast of a rational vector of `g` to a real vector. -/
def realCast (w : (ι₁ → ℚ) × (ι₂ → ℚ)) : (ι₁ → ℝ) × (ι₂ → ℝ) :=
  (fun i => (w.1 i : ℝ), fun k => (w.2 k : ℝ))

/-- The real span `W_ℝ ⊆ g_ℝ` of a rational subspace of `g`. -/
def realSpan (S : Submodule ℚ ((ι₁ → ℚ) × (ι₂ → ℚ))) : Submodule ℝ ((ι₁ → ℝ) × (ι₂ → ℝ)) :=
  Submodule.span ℝ (realCast '' (S : Set ((ι₁ → ℚ) × (ι₂ → ℚ))))

theorem realCast_mem_realSpan {S : Submodule ℚ ((ι₁ → ℚ) × (ι₂ → ℚ))}
    {w : (ι₁ → ℚ) × (ι₂ → ℚ)} (hw : w ∈ S) : realCast w ∈ realSpan S :=
  Submodule.subset_span ⟨w, hw, rfl⟩

theorem realSpan_mono {S T : Submodule ℚ ((ι₁ → ℚ) × (ι₂ → ℚ))} (h : S ≤ T) :
    realSpan S ≤ realSpan T :=
  Submodule.span_mono (Set.image_mono h)

end Real

variable {ι₁ ι₂ : Type*} [Fintype ι₁] {a : Step2Algebra ι₁ ι₂}

/-- A graded `ℚ`-subalgebra `W = W₁ ⊕ W₂` of the graded Lie algebra `g = g₁ ⊕ g₂`, as a
`ℚ`-submodule of `g₁ × g₂` that is stable under the two projections (`W` is basis-graded) and under
the bracket `[x, y] = (0, β(x₁, y₁))`. -/
structure GradedSubalg (a : Step2Algebra ι₁ ι₂) where
  /-- The underlying `ℚ`-submodule of `g₁ × g₂`. -/
  toSubmodule : Submodule ℚ ((ι₁ → ℚ) × (ι₂ → ℚ))
  /-- The layer-one component of an element of `W` lies in `W`. -/
  fst_mem : ∀ w ∈ toSubmodule, (w.1, (0 : ι₂ → ℚ)) ∈ toSubmodule
  /-- The layer-two component of an element of `W` lies in `W`. -/
  snd_mem : ∀ w ∈ toSubmodule, ((0 : ι₁ → ℚ), w.2) ∈ toSubmodule
  /-- `W` is closed under the bracket. -/
  bracket_mem : ∀ x ∈ toSubmodule, ∀ y ∈ toSubmodule,
    ((0 : ι₁ → ℚ), a.br x.1 y.1) ∈ toSubmodule

namespace GradedSubalg

/-- The layer-one part `W₁ = W ∩ g₁`. -/
def layer₁ (W : GradedSubalg a) : Submodule ℚ (ι₁ → ℚ) :=
  W.toSubmodule.comap (LinearMap.inl ℚ (ι₁ → ℚ) (ι₂ → ℚ))

/-- The layer-two part `W₂ = W ∩ g₂`. -/
def layer₂ (W : GradedSubalg a) : Submodule ℚ (ι₂ → ℚ) :=
  W.toSubmodule.comap (LinearMap.inr ℚ (ι₁ → ℚ) (ι₂ → ℚ))

theorem mem_layer₁ {W : GradedSubalg a} {x : ι₁ → ℚ} :
    x ∈ W.layer₁ ↔ (x, (0 : ι₂ → ℚ)) ∈ W.toSubmodule := Iff.rfl

theorem mem_layer₂ {W : GradedSubalg a} {x : ι₂ → ℚ} :
    x ∈ W.layer₂ ↔ ((0 : ι₁ → ℚ), x) ∈ W.toSubmodule := Iff.rfl

theorem ext' {W W' : GradedSubalg a} (h : W.toSubmodule = W'.toSubmodule) : W = W' := by
  cases W
  cases W'
  simp only at h
  subst h
  rfl

/-- `β(W₁, W₁) ⊆ W₂`. -/
theorem br_mem_layer₂ (W : GradedSubalg a) {x y : ι₁ → ℚ} (hx : x ∈ W.layer₁)
    (hy : y ∈ W.layer₁) : a.br x y ∈ W.layer₂ :=
  W.bracket_mem _ hx _ hy

end GradedSubalg

/-- The derived algebra `D = β(g₁, g₁) = [g, g]`, a `ℚ`-subspace of `g₂`. -/
def derived (a : Step2Algebra ι₁ ι₂) : Submodule ℚ (ι₂ → ℚ) :=
  Submodule.span ℚ {z | ∃ x y : ι₁ → ℚ, z = a.br x y}

theorem br_mem_derived (x y : ι₁ → ℚ) : a.br x y ∈ derived a :=
  Submodule.subset_span ⟨x, y, rfl⟩

/-- The graded subalgebra `K = W + D`: `K₁ = W₁` and `K₂ = W₂ + D`. -/
def GradedSubalg.plusDerived (W : GradedSubalg a) : GradedSubalg a where
  toSubmodule := W.toSubmodule ⊔ Submodule.prod ⊥ (derived a)
  fst_mem := by
    intro w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    have hz1 : z.1 = 0 := by simpa using (Submodule.mem_prod.mp hz).1
    have h1 := W.fst_mem y hy
    refine Submodule.mem_sup_left ?_
    simpa [hz1] using h1
  snd_mem := by
    intro w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    refine Submodule.mem_sup.mpr ⟨((0 : ι₁ → ℚ), y.2), W.snd_mem y hy, ((0 : ι₁ → ℚ), z.2),
      Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, (Submodule.mem_prod.mp hz).2⟩, ?_⟩
    ext <;> simp
  bracket_mem := by
    intro x hx y hy
    obtain ⟨x', hx', z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y', hy', z', hz', rfl⟩ := Submodule.mem_sup.mp hy
    have hz1 : z.1 = 0 := by simpa using (Submodule.mem_prod.mp hz).1
    have hz1' : z'.1 = 0 := by simpa using (Submodule.mem_prod.mp hz').1
    refine Submodule.mem_sup_left ?_
    simpa [hz1, hz1'] using W.bracket_mem x' hx' y' hy'

theorem GradedSubalg.le_plusDerived (W : GradedSubalg a) :
    W.toSubmodule ≤ W.plusDerived.toSubmodule :=
  le_sup_left

theorem GradedSubalg.mem_plusDerived_of_derived (W : GradedSubalg a) {z : ι₂ → ℚ}
    (hz : z ∈ derived a) : ((0 : ι₁ → ℚ), z) ∈ W.plusDerived.toSubmodule :=
  Submodule.mem_sup_right (Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hz⟩)

/-- The real span of a graded subalgebra is stable under independent scaling of the two layers. -/
theorem realSpan_scale (W : GradedSubalg a) (s₁ s₂ : ℝ) {y : (ι₁ → ℝ) × (ι₂ → ℝ)}
    (hy : y ∈ realSpan W.toSubmodule) :
    (s₁ • y.1, s₂ • y.2) ∈ realSpan W.toSubmodule := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have h1 := Submodule.smul_mem _ s₁ (realCast_mem_realSpan (W.fst_mem w hw))
    have h2 := Submodule.smul_mem _ s₂ (realCast_mem_realSpan (W.snd_mem w hw))
    have h3 := Submodule.add_mem _ h1 h2
    convert h3 using 1
    ext <;> simp [realCast]
  | zero =>
    have h := Submodule.zero_mem (realSpan W.toSubmodule)
    convert h using 1
    ext <;> simp
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    convert this using 1
    ext <;> simp [mul_add]
  | smul t x _ hx =>
    have := Submodule.smul_mem _ t hx
    convert this using 1
    ext <;> simp <;> ring

/-- `W` is spanned by `d = dim g` vectors of coordinate log-height at most `p`. -/
def GradedSubalg.Gen [Fintype ι₂] (W : GradedSubalg a) (p : ℝ) : Prop :=
  ∃ v : Fin (Fintype.card ι₁ + Fintype.card ι₂) → (ι₁ → ℚ) × (ι₂ → ℚ),
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    ∀ r, (∀ i, ratLogHeight ((v r).1 i) ≤ p) ∧ ∀ k, ratLogHeight ((v r).2 k) ≤ p

theorem GradedSubalg.Gen.mono [Fintype ι₂] {W : GradedSubalg a} {p p' : ℝ}
    (h : W.Gen p) (hpp : p ≤ p') : W.Gen p' := by
  obtain ⟨v, hv, hh⟩ := h
  exact ⟨v, hv, fun r => ⟨fun i => (hh r).1 i |>.trans hpp, fun k => (hh r).2 k |>.trans hpp⟩⟩

/-- The datum `(W; A, M, m)` for `Y` in the symbol group: `Y = E P R` with `E` slow (`|e₁| ≤ M / A`,
`|e₂| ≤ M / A²`), the coordinates of `R` in `(1/m) ℤ`, `P ∈ exp (W_ℝ)`, and `W` spanned by `d`
vectors of coordinate log-height at most `p`. -/
def Datum [Fintype ι₂] (p : ℝ) (W : GradedSubalg a) (A M : ℝ) (m : ℕ) (Y : SymbolGroup a) : Prop :=
  W.Gen p ∧ 0 < m ∧ ∃ E P R : SymbolGroup a, E * P * R = Y ∧
    (∀ i, |E.fst i| ≤ M / A) ∧ (∀ k, |E.snd k| ≤ M / A ^ 2) ∧
    (∀ i, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.fst i) ∧ (∀ k, ∃ z : ℤ, (z : ℝ) = (m : ℝ) * R.snd k) ∧
    (P.fst, P.snd) ∈ realSpan W.toSubmodule

/-- Monotonicity of the datum in the slow scale, the slow constant and the height parameter. -/
theorem Datum.mono [Fintype ι₂] {p p' : ℝ} {W : GradedSubalg a} {A A' M M' : ℝ} {m : ℕ}
    {Y : SymbolGroup a} (h : Datum p W A M m Y) (hpp : p ≤ p') (hA : 0 < A') (hAA : A' ≤ A)
    (hM : 0 ≤ M) (hMM : M ≤ M') : Datum p' W A' M' m Y := by
  obtain ⟨hgen, hm, E, P, R, hprod, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hgen.mono hpp, hm, E, P, R, hprod, fun i => (h1 i).trans ?_, fun k => (h2 k).trans ?_,
    h3, h4, h5⟩
  · exact div_le_div₀ (hM.trans hMM) hMM hA hAA
  · exact div_le_div₀ (hM.trans hMM) hMM (by positivity) (pow_le_pow_left₀ hA.le hAA 2)

/-- **Undilation (Step 0).** If `δ_t Y` has a `W`-datum with `t` a positive integer, then `Y` has a
`W`-datum at the scale `A t` with the grid `(1/(m t²)) ℤ`: the dilation `δ_{t}⁻¹` is an automorphism
of the group that preserves every graded subalgebra. -/
theorem Datum.of_dil [Fintype ι₂] {p : ℝ} {W : GradedSubalg a} {A M : ℝ} {m : ℕ} {Y : SymbolGroup a}
    (t : ℕ) (ht : 1 ≤ t) (hA : 0 < A) (h : Datum p W A M m (SymbolGroup.dil (t : ℝ) Y)) :
    Datum p W (A * t) M (m * t ^ 2) Y := by
  obtain ⟨hgen, hm, E, P, R, hprod, h1, h2, h3, h4, h5⟩ := h
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  refine ⟨hgen, by positivity, SymbolGroup.dil (t : ℝ)⁻¹ E, SymbolGroup.dil (t : ℝ)⁻¹ P,
    SymbolGroup.dil (t : ℝ)⁻¹ R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod]
    exact SymbolGroup.dil_dil_inv ht0.ne' Y
  · intro i
    simp only [SymbolGroup.dil_fst, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv,
      abs_of_pos ht0]
    calc (t : ℝ)⁻¹ * |E.fst i| ≤ (t : ℝ)⁻¹ * (M / A) :=
          mul_le_mul_of_nonneg_left (h1 i) (by positivity)
      _ = M / (A * t) := by field_simp
  · intro k
    simp only [SymbolGroup.dil_snd, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_inv,
      abs_of_pos ht0]
    calc ((t : ℝ)⁻¹) ^ 2 * |E.snd k| ≤ ((t : ℝ)⁻¹) ^ 2 * (M / A ^ 2) :=
          mul_le_mul_of_nonneg_left (h2 k) (by positivity)
      _ = M / (A * t) ^ 2 := by field_simp
  · intro i
    obtain ⟨z, hz⟩ := h3 i
    refine ⟨z * t, ?_⟩
    simp only [SymbolGroup.dil_fst, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [hz]
    field_simp
  · intro k
    obtain ⟨z, hz⟩ := h4 k
    refine ⟨z, ?_⟩
    simp only [SymbolGroup.dil_snd, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [hz]
    field_simp
  · exact realSpan_scale W (t : ℝ)⁻¹ ((t : ℝ)⁻¹ ^ 2) h5

end PrimeCarleson.Proof.Fplus31
