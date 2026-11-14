module

public import PrimeCarleson.Frozen.HeathBrownModel
public import PrimeCarleson.Frozen.GowersNormInterval
public import PrimeCarleson.Proof.Fplus31.C2.CMain
public import PrimeCarleson.Proof.Fplus31.Glue.Assembly

/-!
# Provider for `PrimeCarleson.vonMangoldt_sub_heathBrown_U3`

Proves the statement under the separate name
`PrimeCarleson.Proof.vonMangoldt_sub_heathBrown_U3`.
Only `PrimeCarleson.Frozen.VonMangoldtSubHeathBrownU3` imports this module.

Proof route for [F+] Proposition 3.1: the bound `PrimeCarleson.Proof.Fplus31.cMainBoundPoly` on the
distance of `Λ` from the Cramér model (Leng's type I/II iteration on the quasi-polynomial `U³`
inverse theorem of the vendored `openai/math` library) gives the statement through the
comparison of the Cramér and Heath-Brown models and the triangle inequality
(`vonMangoldt_sub_heathBrown_U3_of_cmainPoly`).
-/

@[expose] public noncomputable section

namespace PrimeCarleson.Proof

/-- [F+] Proposition 3.1: `Λ - Λ_{≤ Q_N}` is small in `U³[N]` with `Q_N = exp((log N)^{1/10})`,
faster than any power of `log N`. -/
theorem vonMangoldt_sub_heathBrown_U3 :
    ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ N : ℕ+, 2 ≤ N →
      gowersNormInterval 3 N
          (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
            heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤
        C * Real.log N ^ (-A) :=
  Fplus31.vonMangoldt_sub_heathBrown_U3_of_cmainPoly Fplus31.cMainBoundPoly

end PrimeCarleson.Proof
