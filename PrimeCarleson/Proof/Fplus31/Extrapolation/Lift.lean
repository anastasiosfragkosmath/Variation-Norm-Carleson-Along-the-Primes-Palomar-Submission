module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.Generators
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Characters
public import PrimeCarleson.Proof.Fplus31.Extrapolation.Pivot

/-!
# Real spans, the datum for `K = W + D` and the Vinogradov constant (the extrapolation step)

Part of the abstract extrapolation (the extrapolation step of the iteration of `C2/CMain.lean`,
proof of [F+] Proposition 3.1). Glue between the pivot functionals, the real span `W_ℝ` of the datum
and the subalgebra `K = W + D`:

* `fnl_fst_realSpan`, `fnl_snd_realSpan`: an integer functional killing the generators of `W`
  (in one layer) kills the corresponding layer of `P ∈ exp (W_ℝ)`;
* `inl_mem_realSpan`, `inr_mem_realSpan`: a real vector in the real span of generators lying in
  one layer of `S` gives an element of `S_ℝ`;
* `Datum.toPlusDerived`: a `W`-datum is a `(W + D)`-datum;
* `exists_vinoSpec_pos`: the Vinogradov constant may be taken `≥ 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

variable {ι₁ ι₂ : Type*} [Fintype ι₁] {a : Step2Algebra ι₁ ι₂}

/-- A functional killing the layer-one parts of the generators of `W` kills the layer-one part of
every point of `W_ℝ`. -/
theorem fnl_fst_realSpan {W : GradedSubalg a} {κ : Type*}
    {v : κ → (ι₁ → ℚ) × (ι₂ → ℚ)} (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (θ : ι₁ → ℤ) (hθ : ∀ k, ∑ i, (θ i : ℚ) * (v k).1 i = 0) {y : (ι₁ → ℝ) × (ι₂ → ℝ)}
    (hy : y ∈ realSpan W.toSubmodule) : fnl θ y.1 = 0 := by
  have hW : ∀ w ∈ W.toSubmodule, ∑ i, (θ i : ℚ) * w.1 i = 0 := by
    intro w hw
    rw [← hv] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hθ k
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Prod.fst_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
    | smul t x _ hx =>
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      have : ∑ i, (θ i : ℚ) * (t * x.1 i) = t * ∑ i, (θ i : ℚ) * x.1 i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hx, mul_zero]
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have h := congrArg (Rat.cast : ℚ → ℝ) (hW w hw)
    simpa [fnl, realCast] using h
  | zero => simp [fnl]
  | add x y _ _ hx hy => simp only [Prod.fst_add, fnl_add, hx, hy, add_zero]
  | smul t x _ hx => simp only [Prod.smul_fst, fnl_smul, hx, mul_zero]

/-- The layer-two version of `fnl_fst_realSpan`. -/
theorem fnl_snd_realSpan [Fintype ι₂] {W : GradedSubalg a} {κ : Type*}
    {v : κ → (ι₁ → ℚ) × (ι₂ → ℚ)} (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (θ : ι₂ → ℤ) (hθ : ∀ k, ∑ i, (θ i : ℚ) * (v k).2 i = 0) {y : (ι₁ → ℝ) × (ι₂ → ℝ)}
    (hy : y ∈ realSpan W.toSubmodule) : fnl θ y.2 = 0 := by
  have hW : ∀ w ∈ W.toSubmodule, ∑ i, (θ i : ℚ) * w.2 i = 0 := by
    intro w hw
    rw [← hv] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hθ k
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
    | smul t x _ hx =>
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      have : ∑ i, (θ i : ℚ) * (t * x.2 i) = t * ∑ i, (θ i : ℚ) * x.2 i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hx, mul_zero]
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have h := congrArg (Rat.cast : ℚ → ℝ) (hW w hw)
    simpa [fnl, realCast] using h
  | zero => simp [fnl]
  | add x y _ _ hx hy => simp only [Prod.snd_add, fnl_add, hx, hy, add_zero]
  | smul t x _ hx => simp only [Prod.smul_snd, fnl_smul, hx, mul_zero]

omit [Fintype ι₁] in
/-- A vector of the real span of layer-one generators of `S` gives a point `(y, 0)` of `S_ℝ`. -/
theorem inl_mem_realSpan {S : Submodule ℚ ((ι₁ → ℚ) × (ι₂ → ℚ))} {κ : Type*} {g : κ → ι₁ → ℚ}
    (hg : ∀ k, (g k, (0 : ι₂ → ℚ)) ∈ S) {y : ι₁ → ℝ}
    (hy : y ∈ Submodule.span ℝ (Set.range fun k i => (g k i : ℝ))) :
    (y, (0 : ι₂ → ℝ)) ∈ realSpan S := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have h := realCast_mem_realSpan (hg k)
    convert h using 1
    exact Prod.ext (funext fun i => by simp [realCast]) (funext fun i => by simp [realCast])
  | zero =>
    rw [Prod.mk_zero_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    simpa using this
  | smul t x _ hx =>
    have := Submodule.smul_mem _ t hx
    simpa using this

omit [Fintype ι₁] in
/-- A vector of the real span of layer-two generators of `S` gives a point `(0, y)` of `S_ℝ`. -/
theorem inr_mem_realSpan {S : Submodule ℚ ((ι₁ → ℚ) × (ι₂ → ℚ))} {κ : Type*} {g : κ → ι₂ → ℚ}
    (hg : ∀ k, ((0 : ι₁ → ℚ), g k) ∈ S) {y : ι₂ → ℝ}
    (hy : y ∈ Submodule.span ℝ (Set.range fun k i => (g k i : ℝ))) :
    ((0 : ι₁ → ℝ), y) ∈ realSpan S := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have h := realCast_mem_realSpan (hg k)
    convert h using 1
    exact Prod.ext (funext fun i => by simp [realCast]) (funext fun i => by simp [realCast])
  | zero =>
    rw [Prod.mk_zero_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    simpa using this
  | smul t x _ hx =>
    have := Submodule.smul_mem _ t hx
    simpa using this

/-- A `W`-datum is a `(W + D)`-datum. -/
theorem Datum.toPlusDerived [Fintype ι₂] {p : ℝ} (hp : 0 ≤ p)
    (hc : ∀ i j k, ratLogHeight (a.c i j k) ≤ p) {W : GradedSubalg a} {A M : ℝ} {m : ℕ}
    {Y : SymbolGroup a} (h : Datum p W A M m Y) : Datum p W.plusDerived A M m Y := by
  obtain ⟨hgen, hm, E, P, R, hprod, h1, h2, h3, h4, h5⟩ := h
  exact ⟨W.gen_plusDerived hp hgen hc, hm, E, P, R, hprod, h1, h2, h3, h4,
    realSpan_mono W.le_plusDerived h5⟩

/-- The Vinogradov constant can be taken at least one. -/
theorem exists_vinoSpec_pos : ∃ C : ℕ, 1 ≤ C ∧ VinoSpec C := by
  obtain ⟨C, hC⟩ := exists_vinoSpec
  refine ⟨C, ?_, hC⟩
  by_contra hlt
  have hC0 : C = 0 := by omega
  subst hC0
  obtain ⟨q, hq0, hq, -⟩ := hC 1 0 one_pos le_rfl (by simp) 0 (by simp) 0 (by simp) ∅
    (by simp) (by simp) (by simp)
  simp at hq
  omega

end PrimeCarleson.Proof.Fplus31
