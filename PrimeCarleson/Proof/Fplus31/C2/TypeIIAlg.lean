module

public import PrimeCarleson.Proof.Fplus31.Extrapolation.MainII

/-!
# The type II step, algebra: transport along an identification of two graded step-two algebras

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
abstract type II extrapolation of the abstract extrapolation (`Extrapolation/MainII.lean`) is stated
for the product `g × g` of the model of `Extrapolation/Model.lean`, whose index types are `ι₁ ⊕ ι₁`
and `ι₂ ⊕ ι₂`. The vendored library's pair model `D × D` has the weight-`k` indices of the product
basis `Fin (card (Σ _ : Fin 2, Fin d))` instead. This file transports the symbol group, graded
subalgebras and data along an equivalence of the index types that matches the structure constants,
and states the frequency facts used by the descending stage:

* `Step2Algebra.IndexEquiv`, `.map`, `.psi`, `GradedSubalg.transport`, `Datum.transport`;
* `frLin`, `frPair`: the layer functional `z ↦ ∑ z k * μ k` and the product functional `(η, -η)`;
* `commonKernel_layer₂_freq`, `commonKernel_layer₁_freq`, `commonKernel_flag`: if `(η, -η)`
  kills the top layer of `W`, then `η` kills the top layer of `K⁰ = (W + D × D)⁰`, provided `η`
  kills `[g, g]` (layer two), and `η` kills the brackets `[k, k']` of the layer one of `K⁰`.

-/

@[expose] public noncomputable section


set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

section Equiv

variable {κ₁ κ₂ ι₁ ι₂ : Type*} [Fintype κ₁] [Fintype ι₁]

/-- An identification of two graded step-two algebras by index equivalences. -/
structure Step2Algebra.IndexEquiv (a' : Step2Algebra κ₁ κ₂) (a : Step2Algebra ι₁ ι₂) where
  /-- The equivalence of the layer-one indices. -/
  e₁ : κ₁ ≃ ι₁
  /-- The equivalence of the layer-two indices. -/
  e₂ : κ₂ ≃ ι₂
  /-- The structure constants correspond. -/
  c_eq : ∀ i j k, a'.c i j k = a.c (e₁ i) (e₁ j) (e₂ k)

variable {a' : Step2Algebra κ₁ κ₂} {a : Step2Algebra ι₁ ι₂} (E : Step2Algebra.IndexEquiv a' a)

/-- The bracket commutes with the reindexing. -/
theorem Step2Algebra.IndexEquiv.br_comp {K : Type*} [Field K] (x y : ι₁ → K) (k : κ₂) :
    a'.br (fun i => x (E.e₁ i)) (fun j => y (E.e₁ j)) k = a.br x y (E.e₂ k) := by
  rw [Step2Algebra.br_apply, Step2Algebra.br_apply]
  simp only [E.c_eq]
  rw [← E.e₁.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← E.e₁.sum_comp]

/-- The bracket commutes with the reindexing, in the inverse direction. -/
theorem Step2Algebra.IndexEquiv.br_comp_symm {K : Type*} [Field K] (x y : κ₁ → K) (k : ι₂) :
    a.br (fun i => x (E.e₁.symm i)) (fun j => y (E.e₁.symm j)) k = a'.br x y (E.e₂.symm k) := by
  have := E.br_comp (K := K) (fun i => x (E.e₁.symm i)) (fun j => y (E.e₁.symm j)) (E.e₂.symm k)
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at this
  exact this.symm

/-- The transport of the symbol group along an index equivalence. -/
def Step2Algebra.IndexEquiv.map : SymbolGroup a' →* SymbolGroup a where
  toFun x := ⟨fun i => x.fst (E.e₁.symm i), fun k => x.snd (E.e₂.symm k)⟩
  map_one' := by
    refine SymbolGroup.ext ?_ ?_ <;> funext i <;> simp
  map_mul' x y := by
    refine SymbolGroup.ext ?_ ?_
    · funext i
      simp
    · funext k
      simp [E.br_comp_symm]

@[simp] theorem Step2Algebra.IndexEquiv.map_fst (x : SymbolGroup a') (i : ι₁) :
    (E.map x).fst i = x.fst (E.e₁.symm i) := rfl

@[simp] theorem Step2Algebra.IndexEquiv.map_snd (x : SymbolGroup a') (k : ι₂) :
    (E.map x).snd k = x.snd (E.e₂.symm k) := rfl

/-- The linear equivalence of the rational vectors. -/
def Step2Algebra.IndexEquiv.psi :
    ((κ₁ → ℚ) × (κ₂ → ℚ)) ≃ₗ[ℚ] ((ι₁ → ℚ) × (ι₂ → ℚ)) :=
  LinearEquiv.prodCongr (LinearEquiv.funCongrLeft ℚ ℚ E.e₁.symm)
    (LinearEquiv.funCongrLeft ℚ ℚ E.e₂.symm)

/-- The transport of a graded subalgebra. -/
def GradedSubalg.transport (W : GradedSubalg a') : GradedSubalg a where
  toSubmodule := W.toSubmodule.comap E.psi.symm.toLinearMap
  fst_mem w hw := by
    have h := W.fst_mem _ hw
    change E.psi.symm (w.1, 0) ∈ W.toSubmodule
    convert h using 1
    rfl
  snd_mem w hw := by
    have h := W.snd_mem _ hw
    change E.psi.symm (0, w.2) ∈ W.toSubmodule
    convert h using 1
    rfl
  bracket_mem x hx y hy := by
    have h := W.bracket_mem _ hx _ hy
    change E.psi.symm (0, a.br x.1 y.1) ∈ W.toSubmodule
    convert h using 1
    refine Prod.ext rfl (funext fun k => ?_)
    exact (E.br_comp x.1 y.1 k).symm

omit [Fintype κ₁] [Fintype ι₁] in
/-- The real span of a subalgebra is carried to the real span of its transport. -/
theorem Step2Algebra.IndexEquiv.realSpan_transport {S : Submodule ℚ ((κ₁ → ℚ) × (κ₂ → ℚ))}
    {y : (κ₁ → ℝ) × (κ₂ → ℝ)} (hy : y ∈ realSpan S) :
    ((fun i => y.1 (E.e₁.symm i), fun k => y.2 (E.e₂.symm k)) : (ι₁ → ℝ) × (ι₂ → ℝ)) ∈
      realSpan (S.comap E.psi.symm.toLinearMap) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have hmem : E.psi w ∈ S.comap E.psi.symm.toLinearMap := by
      change E.psi.symm (E.psi w) ∈ S
      rwa [LinearEquiv.symm_apply_apply]
    exact realCast_mem_realSpan hmem
  | zero =>
    have h := Submodule.zero_mem (realSpan (S.comap E.psi.symm.toLinearMap))
    convert h using 1
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    convert this using 1
  | smul t x _ hx =>
    have := Submodule.smul_mem _ t hx
    convert this using 1

/-- **Transport of the datum.** -/
theorem Datum.transport [Fintype κ₂] [Fintype ι₂] {p A M : ℝ} {m : ℕ} {W : GradedSubalg a'}
    {Y : SymbolGroup a'} (h : Datum p W A M m Y) :
    Datum p (GradedSubalg.transport E W) A M m (E.map Y) := by
  obtain ⟨⟨v, hv, hh⟩, hm, Ee, P, R, hprod, h1, h2, h3, h4, h5⟩ := h
  have hcard : Fintype.card ι₁ + Fintype.card ι₂ = Fintype.card κ₁ + Fintype.card κ₂ := by
    rw [Fintype.card_congr E.e₁, Fintype.card_congr E.e₂]
  refine ⟨⟨fun r => E.psi (v (Fin.cast hcard r)), ?_, fun r => ⟨fun i => (hh _).1 _,
    fun k => (hh _).2 _⟩⟩, hm, E.map Ee, E.map P, E.map R, ?_, fun i => h1 _, fun k => h2 _,
    fun i => h3 _, fun k => h4 _, ?_⟩
  · have hr : Set.range (fun r => E.psi (v (Fin.cast hcard r))) = E.psi '' Set.range v := by
      ext z
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨v (Fin.cast hcard r), ⟨_, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
        exact ⟨Fin.cast hcard.symm r, by simp⟩
    have h1 : Submodule.span ℚ (Set.range (fun r => E.psi (v (Fin.cast hcard r)))) =
        (Submodule.span ℚ (Set.range v)).map E.psi.toLinearMap := by
      rw [hr, Submodule.map_span]
      rfl
    rw [h1, hv]
    change _ = W.toSubmodule.comap E.psi.symm.toLinearMap
    rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]
  · rw [← map_mul, ← map_mul, hprod]
  · exact E.realSpan_transport h5

end Equiv


section Freq

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {a : Step2Algebra ι₁ ι₂}

/-- The linear functional `z ↦ ∑ k, z k * μ k` on the layer-two coordinates. -/
def frLin (μ : ι₂ → ℚ) : (ι₂ → ℚ) →ₗ[ℚ] ℚ where
  toFun z := ∑ k, z k * μ k
  map_add' x y := by
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' t x := by
    simp [Finset.mul_sum, mul_assoc]

/-- The value of `frLin`. -/
theorem frLin_apply (μ : ι₂ → ℚ) (z : ι₂ → ℚ) : frLin μ z = ∑ k, z k * μ k := rfl

/-- The functional `(η, -η)` on the layer-two coordinates of the product. -/
def frPair (μ : ι₂ → ℚ) : (ι₂ ⊕ ι₂ → ℚ) →ₗ[ℚ] ℚ :=
  (frLin μ).comp (LinearMap.funLeft ℚ ℚ Sum.inl) - (frLin μ).comp (LinearMap.funLeft ℚ ℚ Sum.inr)

/-- The value of `frPair`. -/
theorem frPair_apply (μ : ι₂ → ℚ) (z : ι₂ ⊕ ι₂ → ℚ) :
    frPair μ z = frLin μ (fun k => z (Sum.inl k)) - frLin μ (fun k => z (Sum.inr k)) := rfl

/-- `frPair` on a pair of layer-two vectors. -/
theorem frPair_elim (μ : ι₂ → ℚ) (u v : ι₂ → ℚ) :
    frPair μ (Sum.elim u v) = frLin μ u - frLin μ v := by
  simp [frPair_apply]

/-- `(η, -η)` kills the derived algebra of the product when `η` kills that of `g`. -/
theorem frPair_derived (μ : ι₂ → ℚ) (hD : ∀ x y, frLin μ (a.br x y) = 0) {z : ι₂ ⊕ ι₂ → ℚ}
    (hz : z ∈ derived a.prod) : frPair μ z = 0 := by
  have hle : derived a.prod ≤ LinearMap.ker (frPair μ) := by
    rw [derived, Submodule.span_le]
    rintro _ ⟨x, y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hx : x = Sum.elim (fun i => x (Sum.inl i)) (fun i => x (Sum.inr i)) := by
      ext i; rcases i with i | i <;> rfl
    have hy : y = Sum.elim (fun i => y (Sum.inl i)) (fun i => y (Sum.inr i)) := by
      ext i; rcases i with i | i <;> rfl
    rw [hx, hy, Step2Algebra.br_prod, frPair_elim, hD, hD, sub_zero]
  exact hle hz

/-- **The top layer of `K⁰`.**  If `(η, -η)` kills the layer two of `W` (`W` a graded subalgebra
of `g × g`) and `η` kills `[g, g]`, then `η` kills the layer two of `K⁰ = (W + D × D)⁰`. -/
theorem commonKernel_layer₂_freq (μ : ι₂ → ℚ) (hD : ∀ x y, frLin μ (a.br x y) = 0)
    (W : GradedSubalg a.prod)
    (hW : ∀ z, ((0 : ι₁ ⊕ ι₁ → ℚ), z) ∈ W.toSubmodule → frPair μ z = 0) :
    ∀ z ∈ W.plusDerived.commonKernel.layer₂, frLin μ z = 0 := by
  intro z hz
  rw [GradedSubalg.mem_layer₂_commonKernel] at hz
  have h1 := hz.1
  rw [GradedSubalg.mem_layer₂] at h1
  change ((0 : ι₁ ⊕ ι₁ → ℚ), Sum.elim z (0 : ι₂ → ℚ)) ∈
    W.toSubmodule ⊔ Submodule.prod ⊥ (derived a.prod) at h1
  obtain ⟨y, hy, d, hd, hyd⟩ := Submodule.mem_sup.mp h1
  obtain ⟨hd1, hd2⟩ := Submodule.mem_prod.mp hd
  have hd1' : d.1 = 0 := by simpa using hd1
  have hy1 : y.1 = 0 := by
    have := congrArg Prod.fst hyd
    simpa [hd1'] using this
  have hy0 : y = ((0 : ι₁ ⊕ ι₁ → ℚ), y.2) := Prod.ext hy1 rfl
  have hy2 : frPair μ y.2 = 0 := hW _ (by rw [← hy0]; exact hy)
  have hd3 : frPair μ d.2 = 0 := frPair_derived μ hD hd2
  have h2 : y.2 + d.2 = Sum.elim z (0 : ι₂ → ℚ) := congrArg Prod.snd hyd
  have h3 : frPair μ (Sum.elim z (0 : ι₂ → ℚ)) = 0 := by
    rw [← h2, map_add, hy2, hd3, add_zero]
  rw [frPair_elim] at h3
  simpa using h3

omit [Fintype ι₂] in
/-- **The layer one of `K⁰`** (used in degree one, where the top layer is the layer one).  If
`(η, -η)` kills the layer one of `W`, then `η` kills the layer one of `K⁰ = (W + D × D)⁰`. -/
theorem commonKernel_layer₁_freq (μ : ι₁ → ℚ) (W : GradedSubalg a.prod)
    (hW : ∀ z, (z, (0 : ι₂ ⊕ ι₂ → ℚ)) ∈ W.toSubmodule → frPair μ z = 0) :
    ∀ z ∈ W.plusDerived.commonKernel.layer₁, frLin μ z = 0 := by
  intro z hz
  rw [GradedSubalg.mem_layer₁_commonKernel, GradedSubalg.plusDerived_layer₁] at hz
  have := hW (Sum.elim z 0) (GradedSubalg.mem_layer₁.mp hz.1)
  rw [frPair_elim] at this
  simpa using this

/-- **The flag for `K⁰`.**  If `(η, -η)` kills the layer two of `W`, then `η` kills `[k, k']` for
`k, k'` in the layer one of `K⁰ = (W + D × D)⁰`. -/
theorem commonKernel_flag (μ : ι₂ → ℚ) (W : GradedSubalg a.prod)
    (hW : ∀ z, ((0 : ι₁ ⊕ ι₁ → ℚ), z) ∈ W.toSubmodule → frPair μ z = 0) {k k' : ι₁ → ℚ}
    (hk : k ∈ W.plusDerived.commonKernel.layer₁) (hk' : k' ∈ W.plusDerived.commonKernel.layer₁) :
    frLin μ (a.br k k') = 0 := by
  obtain ⟨h1, -⟩ := GradedSubalg.exposure_commonKernel W hk hk'
  rw [GradedSubalg.mem_layer₂] at h1
  have := hW _ h1
  rw [frPair_elim] at this
  simpa using this

end Freq

end PrimeCarleson.Proof.Fplus31
