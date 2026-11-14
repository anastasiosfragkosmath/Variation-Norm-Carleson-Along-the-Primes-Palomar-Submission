module

public import PrimeCarleson.Proof.Fplus31.C2.DescentIIStep
public import PrimeCarleson.Proof.Fplus31.C2.TypeIGlue

/-!
# The iteration, the flag and the output of a sub-step

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1). The
potential of the iteration is the flag `CommKilled η`: the frequency `η` kills all brackets of the
Lie algebra (`η ⁅x, y⁆ = 0`). The two facts that bound the number of stages:

* `flagGr_of_commKilled`: `CommKilled η` makes `η` kill `[gr, gr]` (so the top layer of
  `K ⊇ [gr, gr]` is killed, and the stage descends in degree);
* `commKilled_refiltered`: whatever the stage, the frequency `η ∘ incl` of the refiltered sub-model
  of a `K` with `η [K, K] = 0` has the flag (once the flag holds it is kept).

`CellOutput s e flag A b` is what the sub-steps `exists_substep` (type I) and
`exists_substep_typeII` give, in the form the pigeonhole over the cells consumes, for the
function `e` the niltest evaluates (`e x = S.T.eval (fun _ => x)`): a period `P ≤ e^b`, and for
every base point `y` of the window a vertical niltest `V` with the flag (the stay branch), or,
when the flag holds, a niltest of degree `s` (the drop branch), approximating `e` on the cell
`x ≡ y (P)`.
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration

/-- **The flag**: the frequency `η` kills every bracket. -/
def CommKilled {L : Type*} [LieRing L] [LieAlgebra ℚ L] (η : L →ₗ[ℚ] ℚ) : Prop :=
  ∀ x y : L, η ⁅x, y⁆ = 0

section Flag

variable {ι L : Type*} [Finite ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

omit [Finite ι] in
/-- The graded frequency of the bracket of two pieces of weight one is `η ⁅u, v⁆`. -/
theorem gradedFrequency_piece_lie (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ)
    (u v : F.layer 1) :
    F.gradedFrequency b ω hF η ⁅F.associatedGradedPieceMap 1 u, F.associatedGradedPieceMap 1 v⁆ =
      η ⁅(u : L), (v : L)⁆ := by
  rw [F.associatedGradedPieceMap_lie 1 1 u v]
  rcases Nat.lt_or_ge s 2 with hlt | hge
  · obtain rfl : s = 1 := by omega
    have h0 : (⁅(u : L), (v : L)⁆) = 0 := by
      have := F.lie_mem u.property v.property
      have h2 : F.layer 2 = ⊥ := F.terminal
      rw [h2] at this
      simpa using this
    have h0' : (⟨⁅(u : L), (v : L)⁆, F.lie_mem u.property v.property⟩ : F.layer (1 + 1)) = 0 :=
      Subtype.ext h0
    rw [h0', map_zero, map_zero, h0, map_zero]
  · obtain rfl : s = 2 := by omega
    exact F.gradedFrequency_top_piece b ω hF η ⟨⁅(u : L), (v : L)⁆, F.lie_mem u.property v.property⟩

/-- **`CommKilled η` makes `η` kill `[gr, gr]`** (the hypothesis of the top-kill clause of the
sub-steps). -/
theorem flagGr_of_commKilled (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ) (h : CommKilled η) :
    ∀ z ∈ commutatorSubmodule F.AssociatedGraded, F.gradedFrequency b ω hF η z = 0 := by
  have hB := step2Graded_associatedGraded F b ω hF hs2
  have hle : commutatorSubmodule F.AssociatedGraded ≤
      LinearMap.ker (F.gradedFrequency b ω hF η) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, lie_eq_lie_gradeProjection_one hB x y]
    obtain ⟨u, hu⟩ := F.exists_associatedGradedPieceMap_of_pure b ω hF 1 _
      (gradeProjection_idem (F.associatedGradedBasis b ω hF) ω 1 x)
    obtain ⟨v, hv⟩ := F.exists_associatedGradedPieceMap_of_pure b ω hF 1 _
      (gradeProjection_idem (F.associatedGradedBasis b ω hF) ω 1 y)
    rw [← hu, ← hv, gradedFrequency_piece_lie F b ω hF hs1 hs2 η u v]
    exact h _ _
  exact fun z hz => hle hz

omit [Finite ι] in
/-- **The flag of the refiltered sub-model.**  If `η [K, K] = 0` in the graded algebra, the
frequency `η ∘ incl` of the refiltered subalgebra `gradedRefiltrationSubalgebra K` kills all
brackets. -/
theorem commKilled_refiltered (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (η : L →ₗ[ℚ] ℚ)
    (K : LieSubalgebra ℚ F.AssociatedGraded)
    (hc : ∀ x ∈ K, ∀ y ∈ K, F.gradedFrequency b ω hF η ⁅x, y⁆ = 0) :
    CommKilled (η.comp (F.gradedRefiltrationSubalgebra K).incl.toLinearMap) := by
  intro x y
  have hx : (x : L) ∈ F.gradedRefiltrationLayer K 1 := x.property
  have hy : (y : L) ∈ F.gradedRefiltrationLayer K 1 := y.property
  have hx1 : (x : L) ∈ F.layer 1 := F.gradedRefiltrationLayer_le K 1 hx
  have hy1 : (y : L) ∈ F.layer 1 := F.gradedRefiltrationLayer_le K 1 hy
  have hxK := (F.mem_gradedRefiltrationLayer_iff K 1 ⟨x, hx1⟩).mp hx
  have hyK := (F.mem_gradedRefiltrationLayer_iff K 1 ⟨y, hy1⟩).mp hy
  have h := hc _ hxK _ hyK
  rw [gradedFrequency_piece_lie F b ω hF hs1 hs2 η ⟨x, hx1⟩ ⟨y, hy1⟩] at h
  simpa using h

end Flag

/-- **The output of a sub-step**, for the function `e : ℤ → ℂ` evaluated by the niltest: a period
`P ≤ e^b` and, for every base point `y` of the window `|y| ≤ A`, a vertical niltest `V` of
degree `s + 1` and complexity `b` with the flag `CommKilled V.η` (stay), or, if `flag` holds, a
niltest of degree `s` and complexity `b` (drop), with `‖e x - V.eval x‖ ≤ e^b δ` on the cell
`x ≡ y (P)`, `|x - y| ≤ A δ`. -/
def CellOutput (s : ℕ) (e : ℤ → ℂ) (flag : Prop) (A b : ℝ) : Prop :=
  (∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧ ∀ y : ℤ, |(y : ℝ)| ≤ A →
      ∃ V : VerticalNiltest (s + 1) b, CommKilled V.η ∧
        ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
          |(x : ℝ) - y| ≤ A * δ → ‖e x - V.T.eval (fun _ => x)‖ ≤ Real.exp b * δ) ∧
  (flag → ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧ ∀ y : ℤ, |(y : ℝ)| ≤ A →
      ∃ N : NiltestData s, N.T.ComplexityLE b ∧ N.T.normBound ≤ 1 ∧
        ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
          |(x : ℝ) - y| ≤ A * δ → ‖e x - N.T.eval (fun _ => x)‖ ≤ Real.exp b * δ)

/-- **From the kernel `K` to `CellOutput`.**  The sub-step gives a `K` with `η [K, K] = 0` and the
conditional top-kill clause, a stay branch on the refiltered sub-model and a drop branch under the
top-kill; with `CommKilled S.η` as the flag this is a `CellOutput`. -/
theorem cellOutput_of_kernel {s : ℕ} (hs : s ≤ 1) {Q : Finset (Unit → ℤ)}
    {f : (Unit → ℤ) → ℂ} {p : ℝ} (S : LengStart (s + 1) Q f p) {A b : ℝ}
    (K : LieSubalgebra ℚ S.D.filtration.AssociatedGraded)
    (hc : ∀ x ∈ K, ∀ y ∈ K,
      S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η ⁅x, y⁆ = 0)
    (hd : (∀ z ∈ commutatorSubmodule S.D.filtration.AssociatedGraded,
        S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η z = 0) →
      ∀ x ∈ K, basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis S.omega
        S.hF) S.omega (s + 1) x = x →
        S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η x = 0)
    (hstay : ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧ ∀ y : ℤ, |(y : ℝ)| ≤ A →
      ∃ V : SubModelNiltest S.D K S.η b,
        ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
          |(x : ℝ) - y| ≤ A * δ →
          ‖S.T.eval (fun _ => x) - V.toVertical.T.eval (fun _ => x)‖ ≤ Real.exp b * δ)
    (hdrop : (∀ x ∈ K, basisGradeProjection (S.D.filtration.associatedGradedBasis S.D.basis
        S.omega S.hF) S.omega (s + 1) x = x →
        S.D.filtration.gradedFrequency S.D.basis S.omega S.hF S.η x = 0) →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧ ∀ y : ℤ, |(y : ℝ)| ≤ A →
        ∃ N : NiltestData s, N.dim ≤ finrank ℚ
            (S.D.filtration.gradedRefiltrationSubalgebra K) ∧
          N.T.ComplexityLE b ∧ N.T.normBound ≤ 1 ∧
          ∀ (x : ℤ) (δ : ℝ), 0 ≤ δ → |(x : ℝ)| ≤ A → (P : ℤ) ∣ x - y →
            |(x : ℝ) - y| ≤ A * δ →
            ‖S.T.eval (fun _ => x) - N.T.eval (fun _ => x)‖ ≤ Real.exp b * δ) :
    CellOutput s (fun x => S.T.eval (fun _ => x)) (CommKilled S.η) A b := by
  refine ⟨?_, fun hflag => ?_⟩
  · obtain ⟨P, hP, hPb, hmod⟩ := hstay
    refine ⟨P, hP, hPb, fun y hy => ?_⟩
    obtain ⟨V, hV⟩ := hmod y hy
    exact ⟨V.toVertical, commKilled_refiltered S.D.filtration S.D.basis S.omega S.hF
      (by omega) (by omega) S.η K hc, hV⟩
  · have hflagGr := flagGr_of_commKilled S.D.filtration S.D.basis S.omega S.hF (by omega)
      (by omega) S.η hflag
    obtain ⟨P, hP, hPb, hmod⟩ := hdrop (hd hflagGr)
    refine ⟨P, hP, hPb, fun y hy => ?_⟩
    obtain ⟨N, -, hNc, hNn, hN⟩ := hmod y hy
    exact ⟨N, hNc, hNn, hN⟩

end PrimeCarleson.Proof.Fplus31
