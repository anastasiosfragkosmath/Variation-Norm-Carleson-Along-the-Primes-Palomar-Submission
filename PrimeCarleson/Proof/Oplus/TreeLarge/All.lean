module

public import PrimeCarleson.Proof.Oplus.TreeLarge.Fourier
public import PrimeCarleson.Proof.Oplus.TreeLarge.Variation
public import PrimeCarleson.Proof.Oplus.TreeLarge.Scales
public import PrimeCarleson.Proof.Oplus.TreeLarge.Maximal
public import PrimeCarleson.Proof.Oplus.TreeLarge.Blocks
public import PrimeCarleson.Proof.Oplus.TreeLarge.LocalMax
public import PrimeCarleson.Proof.Oplus.TreeLarge.Overlapping
public import PrimeCarleson.Proof.Oplus.TreeLarge.LargeIntervals
public import PrimeCarleson.Proof.Oplus.TreeLarge.Special
public import PrimeCarleson.Proof.Oplus.TreeLarge.Reduction
public import PrimeCarleson.Proof.Oplus.TreeLarge.TreeEstimate

/-!
# The tree estimate on large intervals and the assembly of the tree estimate

[O+] L2011-L2445:

* `treeestimate` (`TreeEstimate.lean`, `treeestimate`), its reduction to special trees
  (`Reduction.lean`, `exists_special_decomposition`) and the assembly (`Special.lean`,
  `treeestimate_special_pow`);
* `treeestimatelargeintervals` (`LargeIntervals.lean`, `treeestimate_large_intervals_sum`),
  the overlapping case (`Overlapping.lean`, `overlapping_case_sum`),
  the integration over `J` (`overlapping_per_J`), the maximal function and variation `L²` bounds
  (`overlapping_sum_le_L2`, `Maximal.lean`, `lintegral_maximalHLR_varW_le`),
  the local maximal bound (`LocalMax.lean`, `rVariationOn_schwartzAvg_le_maximalHLR`, with
  `Fourier.lean`, `schwartzAvg_reproduce`, and `Maximal.lean`,
  `lintegral_schwartzScale_le_maximalHLR`), the variation in the scale parameter
  (`Blocks.lean`, `variation_in_scale_parameter`, with `Variation.lean`,
  `sum_blocks_le_rVariationOn`), `schwartzchoice` and its frequency localization
  (`Fourier.lean`, `schwartzAvg_modTreeFn`);
* `intervalofscales` and `intervalofscales2` (`Blocks.lean`, `block_convex`, with `Scales.lean`).
-/
