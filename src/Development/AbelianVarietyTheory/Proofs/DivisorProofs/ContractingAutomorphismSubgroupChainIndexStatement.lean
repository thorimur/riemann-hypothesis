import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutomorphismSubgroupChainIndex
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracting_automorphism_subgroup_chain_index : GlobalTheory.SatakeWeyl.ChainIndex := by
  first | exact @GlobalTheory.SatakeWeyl.chainIndex | exact GlobalTheory.SatakeWeyl.chainIndex | (intros; apply GlobalTheory.SatakeWeyl.chainIndex <;> assumption)
