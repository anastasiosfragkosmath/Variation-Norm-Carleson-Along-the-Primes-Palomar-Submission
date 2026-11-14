module

public import PrimeCarleson.Proof.Oplus.ModelBound.Classes

/-!
# The model-operator bounds

Aggregator of the modules of `PrimeCarleson/Proof/Oplus/ModelBound/` (namespace
`PrimeCarleson.Proof.Oplus`); [O+] L1092-L1290 and L879-L880 (in the amended form used here);
Source: [O+] `halfgbound`, L1138–L1144; [O+] `halfgbound`, L1155–L1158; [O+] `halfgbound`,
L1265–L1282; [O+] `csrhobound`, L1092–L1096; [O+] `csrhobound`, L1134–L1137; [O+] `csrhobound`,
L1097–L1098.

* `Dilation`: the dilation `x ↦ 2^j x` of multitiles, linearizing data and the model operator
  (`Multitile.modelOp_dil`) and `halfgbound_separated` (the rescaling of L1155–L1158: every `E`,
  from `1 ≤ |E| ≤ 2`);
* `Separation`: the colouring of the multitiles into `s ⌈C₁⌉` separated classes
  (`exists_separated_colouring`; `60` classes for the constants of [O+]) (the splitting of
  L1265–L1282);
* `LevelSet`: the level set bound `levelSet_separated` and `levelSet_family` (the level set
  reduction of L1134–L1153, for a separated family and for every finite family);
* `Weak`: `csrhobound_oneOrTwo` (1- and 2-indices, no condition on `Ξ`), `levelSet_three`,
  `csrhobound_three` (3-indices by symmetry, L1097–L1121), `csrhobound`;
* `Interpolation`: `model_strong_type` (the strong `L^p` bound for
  `r' < p < 2r/(r-2)` for every index with `m, n ∈ {1, …, 4}`, every profile choice, finite
  family and linearizing data with `Ξ` free of dyadic end points);
* `Classes`: the forms used downstream, `classOp_strong_type` (the ten classes `ρ ∈ R` of a finite
  family of tiles) and `waveOp_strong_type` (`‖𝒮''_𝔓 f‖_{L^p} ≤ 10 C ‖f‖_{L^p}`). -/
