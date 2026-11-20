import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainOccurringParamsNormHalfRankBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBoundW D := by
  first | exact @GlobalTheory.ChainOnto.parBoundW | exact GlobalTheory.ChainOnto.parBoundW | (intros; apply GlobalTheory.ChainOnto.parBoundW <;> assumption)
