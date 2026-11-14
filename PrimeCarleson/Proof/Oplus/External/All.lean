module

public import PrimeCarleson.Proof.Oplus.External.FSInterpolation
public import PrimeCarleson.Proof.Oplus.External.TileEnergy

/-!
# The two remaining external inputs of [O+] (Section 7)

Aggregator of the modules of `PrimeCarleson/Proof/Oplus/External/` (namespace
`PrimeCarleson.Proof.Oplus`):

* The Fefferman–Stein interpolation between `L¹` and dyadic BMO ([O+] L2603–L2609, used for the
  `L^q` bound for the covering function in the large-`F` case of `L1except`; proved here by a
  dyadic stopping-time argument): `Stopping` (maximal dyadic intervals), `FSLevelSets` (Steps 1-3:
  weak type and geometric decay of `{M_D g > λ}`), `FSDistribution` (distribution function),
  `FSLayerCake` (Step 5, the `L^q` estimate), `FSInterpolation` (`dyadic_interpolation`,
  `dyadic_interpolation_indicators`, `dyadic_interpolation_dilates`);
* The tile-energy lemma of Grafakos–Tao–Terwilleger (Source: [O+] `tilessmallmaxprop`,
  L2456–L2465, in the repaired form, used for the energy bound in the small-`F` case of `L1except`):
  `THMaximal` (the superlevel set `Ω_λ`), `THSums` (almost-diagonal sums), `THCalderon`
  (Calderón–Zygmund intervals), `THGood` (good function), `THTerms` (bad parts), `THAssembly`
  (abstract tile-energy bound), `TileEnergyPackets` (modulated wave packets), `TileEnergy`
  (`exists_tile_energy_le_of_subset`, `exists_energy_le_of_not_subset`).
-/

