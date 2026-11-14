module

public import PrimeCarleson.Proof.Oplus.DensityIncrement.Basic
public import PrimeCarleson.Proof.Oplus.DensityIncrement.Selection
public import PrimeCarleson.Proof.Oplus.DensityIncrement.Disjoint
public import PrimeCarleson.Proof.Oplus.DensityIncrement.Truncation
public import PrimeCarleson.Proof.Oplus.DensityIncrement.Covering
public import PrimeCarleson.Proof.Oplus.DensityIncrement.Summation
public import PrimeCarleson.Proof.Oplus.DensityIncrement.Main

/-!
# The density increment proposition of the [O+] proof

Aggregator of the modules of `PrimeCarleson/Proof/Oplus/DensityIncrement/` (namespace
`PrimeCarleson.Proof.Oplus`), [O+] L1895-L1967:

* `Basic`: the density integral `densityExpr` of (treehaslargedensity), dense trees, the shifted
  top data of `T_j^±`;
* `Selection`: the selection algorithm (`IsDensitySelection`, `exists_density_selection`);
* `Disjoint`: the disjointness of the selected tiles (`IsDensitySelection.tiles_disjoint`);
* `Truncation`: `trunctreehaslargedensity` (`exists_trunc_density`);
* `Covering`: the local counting estimate (`covering_local_count`, `exists_covering_rep`,
  `covering_fiber_bound`);
* `Summation`: the summation over `ℓ` and `thirddtreeintervalbound`
  (`IsDensitySelection.thirddtreeintervalbound`);
* `Main`: `densityincrementprop` (`density_increment`).
-/
