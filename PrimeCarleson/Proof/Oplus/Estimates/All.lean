module

public import PrimeCarleson.Proof.Oplus.Estimates.WavePacketBound
public import PrimeCarleson.Proof.Oplus.Estimates.SchwartzEstimate
public import PrimeCarleson.Proof.Oplus.Estimates.SameInterval
public import PrimeCarleson.Proof.Oplus.Estimates.TreeObs
public import PrimeCarleson.Proof.Oplus.Estimates.UnivBound

/-!
# The wave-packet estimates of the [O+] proof

Aggregator of the modules of `PrimeCarleson/Proof/Oplus/Estimates/` (namespace
`PrimeCarleson.Proof.Oplus`):

* `WavePacketBound`: [O+] `wavepacketadaptedbound` (`IsProfile.exists_adaptedBound`,
  `ProfileChoice.exists_adaptedBound`, `Multitile.exists_adaptedBound`) and the weight `w_I`;
* `SchwartzEstimate`: `schwartzestimate` (`Multitile.exists_norm_pairing_wavePacket_le`);
* `SameInterval`: the orthogonality of wave packets with a common time interval (L1766–L1776,
  L2500–L2504) (`Multitile.sum_norm_sq_coeff_le`);
* `TreeObs`: `treeobs` (`treeobs_overlapping`, `treeobs_disjoint_time`,
  `treeobs_disjoint_dilate`);
* `UnivBound`: `univ-den-ene-bound` (L1357–L1400), with tree orthogonality and the far-field tail.
-/
