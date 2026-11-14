module

public import PrimeCarleson.Proof.Fplus31.PNTSW.Inputs
public import PrimeCarleson.Proof.Fplus31.PNTSW.PntAp
public import PrimeCarleson.Proof.Fplus31.PNTSW.Target

/-!
# The prime number theorem in progressions on the classical zero-free region, no Siegel zeros

This is the prime number theorem in progressions used in the proof of [F+] Proposition 3.1, in the
form consumed by the iteration of `C2/` (`C2/CMainFacts.lean`, `termOK_of_large`).

It is founded on the classical de la Vallée Poussin zero-free region and the absence of Siegel
zeros. The final closure of the module imports no module of `OAI.NumberTheory.DirichletL` other than
the standalone `OAI.NumberTheory.DirichletL.LogarithmicControl` (a Mathlib-only file).

The two analytic inputs are the named `Prop`s of `PNTSW.Inputs`:

* `ClassicalZeroFreeRegion`: `L(s, χ) ≠ 0` for `re s ≥ 1 - c / log (q (|im s| + 3))` for
  primitive `χ` modulo `q`, except for a real zero of a real character;
* `NoSiegelZero`: `c ≤ (1 - β) log q` for a real zero `β ∈ (0, 1)` of a real primitive character
  modulo `q ≥ 3` (the statement of
  `OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap`).

The final statements, all conditional on these two inputs only:

* `PNTSW.PntAp.pnt_ap_sw`: `ψ(x; q, a) = [(a, q) = 1] x/φ(q) + O(x exp (-c √(log x)))`, uniformly
  for `log q ≤ c √(log x)`;
* `PNTSW.Target.c5_target_sw`, `c5_terminal_sw`: the target and terminal statements consumed by the
  iteration of `C2/` (`C2/CMainFacts.lean`).

Proof outline: the exact Riesz-mean Perron formula on `re s = 1 + a/4` (`PNTSW.Perron`), the
truncation at height `T = exp √(log y)` and a rectangle contour to `re s = 1 - a/2` (`PNTSW.Rect`),
the Landau bound `‖L'/L‖ ≪ log²(qT)` from Borel-Carathéodory on discs of radius `~ 1/log(qT)`
(`PNTSW.Landau`, `PNTSW.LogDeriv`), orthogonality (`PNTSW.ApRiesz`), the monotone sandwich
(`PNTSW.PntAp`), and the range split and Brun's sieve (`PNTSW.Target`, `brun_ap`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Fplus31.PNTSW

end PrimeCarleson.Proof.Fplus31.PNTSW
