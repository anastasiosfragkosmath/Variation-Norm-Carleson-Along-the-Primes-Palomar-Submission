module

public import PrimeCarleson.Proof.Fplus31.C2.IterationFlag

/-!
# The iteration, translates

Part of the type I / type II iteration of `C2/CMain.lean` (proof of [F+] Proposition 3.1).
`Niltest.translate` shifts the variable and preserves the symbol, the complexity and the observable,
so the extrapolation step and the sub-step are applied to each window centre `z` (a block of the
pigeonhole) with the same extrapolated symbol factorization; and the output niltest of a window is
translated back by `-z`.

* `LengStart.shift`: the `LengStart` of the shifted function and progression, with the shifted
  niltest `x ↦ T.eval (x + z)`;
* `VerticalNiltest.shift`, `NiltestData.shift`: the shifted niltests (the frequency, the
  flag, the complexity and the norm bound are unchanged).
-/

@[expose] public noncomputable section

open OAI OAI.Erdos3
open scoped TensorProduct BigOperators

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31

open Module NilpotentLieFiltration RationalFilteredNilmanifold

/-- The constant shift `fun _ => z` of one-variable points. -/
def shiftPt (z : ℤ) : Unit → ℤ := fun _ => z

section Shift

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

/-- The niltest `x ↦ T.eval (x + z)`. -/
def shiftNiltest (T : D.Niltest (fun _ : Unit => 1)) (z : ℤ) : D.Niltest (fun _ : Unit => 1) :=
  T.translate (fun _ => Nat.one_pos) (shiftPt z)

/-- The shifted niltest evaluates `T` at `x + z`. -/
theorem eval_shiftNiltest (T : D.Niltest (fun _ : Unit => 1)) (z x : ℤ) :
    (shiftNiltest T z).eval (fun _ => x) = T.eval (fun _ => x + z) := by
  unfold shiftNiltest
  rw [Niltest.eval_translate]
  rfl

end Shift

/-- The vertical niltest `x ↦ V.T.eval (x + z)`. -/
def VerticalNiltest.shift {deg : ℕ} {p : ℝ} (V : VerticalNiltest deg p) (z : ℤ) :
    VerticalNiltest deg p where
  L := V.L
  dim := V.dim
  D := V.D
  T := shiftNiltest V.T z
  η := V.η
  complexity := V.complexity
  norm_le := V.norm_le
  eta_height := V.eta_height
  vertical := V.vertical

/-- The shift of a vertical niltest evaluates the original at `x + z`. -/
theorem VerticalNiltest.eval_shift {deg : ℕ} {p : ℝ} (V : VerticalNiltest deg p) (z x : ℤ) :
    (V.shift z).T.eval (fun _ => x) = V.T.eval (fun _ => x + z) :=
  eval_shiftNiltest V.T z x

/-- The niltest `x ↦ N.T.eval (x + z)`. -/
def NiltestData.shift {deg : ℕ} (N : NiltestData deg) (z : ℤ) : NiltestData deg where
  L := N.L
  dim := N.dim
  D := N.D
  T := shiftNiltest N.T z

/-- The shift of a niltest datum evaluates the original at `x + z`. -/
theorem NiltestData.eval_shift {deg : ℕ} (N : NiltestData deg) (z x : ℤ) :
    (N.shift z).T.eval (fun _ => x) = N.T.eval (fun _ => x + z) :=
  eval_shiftNiltest N.T z x

/-- **The shifted `LengStart`**: the niltest `x ↦ T.eval (x + z)` correlates with
`x ↦ f (x + z)` on the shifted set `Q - z`, with the same complexity, symbol and frequency. -/
def LengStart.shift {deg : ℕ} {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
    (S : LengStart deg Q f p) (z : ℤ) :
    LengStart deg (Q.image fun x => x - shiftPt z) (fun x => f (x + shiftPt z)) p where
  L := S.L
  dim := S.dim
  D := S.D
  omega := S.omega
  hF := S.hF
  T := shiftNiltest S.T z
  η := S.η
  complexity := S.complexity
  norm_le := S.norm_le
  eta_height := S.eta_height
  vertical := S.vertical
  eta_ne := S.eta_ne
  corr := by
    have hinj : Set.InjOn (fun x : Unit → ℤ => x - shiftPt z) (Q : Set (Unit → ℤ)) :=
      fun a _ b _ h => by simpa using h
    rw [Finset.expect_image hinj]
    have hev : ∀ x : Unit → ℤ, (shiftNiltest S.T z).eval (x - shiftPt z) = S.T.eval x := by
      intro x
      unfold shiftNiltest
      rw [Niltest.eval_translate, sub_add_cancel]
    simp only [hev, sub_add_cancel]
    exact S.corr

/-- The shifted `LengStart` has the same symbol as the original. -/
theorem LengStart.symbol_shift {deg : ℕ} {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
    (S : LengStart deg Q f p) (z : ℤ) :
    (S.shift z).T.symbol S.D.basis S.omega S.hF = S.T.symbol S.D.basis S.omega S.hF :=
  Niltest.symbol_translate S.T S.D.basis S.omega S.hF (fun _ => Nat.one_pos) (shiftPt z)

/-- The shifted `LengStart` evaluates the original at `x + z`. -/
theorem LengStart.eval_shift {deg : ℕ} {Q : Finset (Unit → ℤ)} {f : (Unit → ℤ) → ℂ} {p : ℝ}
    (S : LengStart deg Q f p) (z x : ℤ) :
    (S.shift z).T.eval (fun _ => x) = S.T.eval (fun _ => x + z) :=
  eval_shiftNiltest S.T z x

end PrimeCarleson.Proof.Fplus31
