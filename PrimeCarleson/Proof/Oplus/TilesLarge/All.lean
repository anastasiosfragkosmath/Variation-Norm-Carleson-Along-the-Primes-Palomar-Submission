module

public import PrimeCarleson.Proof.Oplus.TilesLarge.Sparsity
public import PrimeCarleson.Proof.Oplus.TilesLarge.Coefficients
public import PrimeCarleson.Proof.Oplus.TilesLarge.SingleScale
public import PrimeCarleson.Proof.Oplus.TilesLarge.Packing
public import PrimeCarleson.Proof.Oplus.TilesLarge.Main

/-!
# The auxiliary tile estimate `tileslargemaxprop` of the [O+] proof

Aggregator of the modules of `PrimeCarleson/Proof/Oplus/TilesLarge/` (namespace
`PrimeCarleson.Proof.Oplus`), the proof of [O+] `tileslargemaxprop` (L2469-L2547):

* `Sparsity`: the sparsity of `F` near a scale (L2510–L2512)
  (`volume_inter_dilate_le_of_not_subset`, and the weighted form
  `integral_weight_inter_le_of_not_subset`);
* `Coefficients`: the `ℓ²`, `sup` and `ℓ^r` coefficient bounds (L2487–L2525)
  (`exists_sqrt_sum_norm_sq_coeff_le`, `exists_norm_coeff_le_sup` and
  `exists_rpow_sum_norm_coeff_le`); the same-interval orthogonality is
  `Multitile.sum_norm_sq_coeff_le` of `Estimates/SameInterval.lean`;
* `SingleScale`: the single-scale `L¹` bound (L2526–L2536) (`exists_eLpNorm_single_scale_le`);
* `Packing`: the packing half of the sum over intervals and scales (L2538–L2546)
  (`sum_ofReal_length_le_of_scale`);
* `Main`: the summation over the scales and the weak `(1, 1)` bound of the second half of
  the sum over intervals and scales, and `tileslargemaxprop` itself (`tileslargemaxprop`,
  `tileslargemaxprop_treeSum`).
-/
