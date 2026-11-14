module

public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Basic
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Selection
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Geometry
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Disjointness
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.TailWeight
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.TailSum
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Orthogonality
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.SquareSum
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.SquareByFct
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.IntervalBound
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.FarBessel
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoGeometry
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoSetup
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoMain
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.BmoError
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.PisaGeometry
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.PisaTerms
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.PisaThird
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.PisaTree
public import PrimeCarleson.Proof.Oplus.EnergyIncrement.Main

/-!
# The energy increment proposition of the [O+] proof

Aggregator of the modules of `PrimeCarleson/Proof/Oplus/EnergyIncrement/` (namespace
`PrimeCarleson.Proof.Oplus`):

* `Basic`, `Selection`: energy utilities and the selection algorithm of [O+]
  `energyincrementprop` (`IsSelection`, `exists_selection`);
* `Geometry`, `Disjointness`: interval geometry and `claimofdisjointness` (`claim_pair`);
* `TailWeight`, `TailSum`: the tail weight sum of [O+] L1627–L1644;
* `Orthogonality`, `SquareSum`, `SquareByFct`, `IntervalBound`: the content of `etreeorth1`,
  `etreeorth2`, `etreeorth22`, `squarebyfct` and `claimofdisjointness` as abstract bounds, and
  `etreeintervalbound` (printed form);
* `FarBessel`: `sumafterorth`; `BmoGeometry`, `BmoSetup`, `BmoMain`, `BmoError`:
  `bmosummeasures`, `sumITinTprime`, `squarebyfctanalog`, `sumTj`, `etreebmobound`
  (the dyadic BMO norm `dyadicBMO`);
* `PisaGeometry`, `PisaTerms`, `PisaThird`, `PisaTree`: `threeterms`, `pisatree` and its three
  terms;
* `Main`: `energyincrementprop` (`energy_increment`).
-/
