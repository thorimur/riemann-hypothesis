import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainRealZetaNonvanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_realZeta_nonvanishing : GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D → GlobalTheory.ChainOnto.RealZeta D := by
  first | exact @GlobalTheory.RealZetaProof.realZeta | exact GlobalTheory.RealZetaProof.realZeta | (intros; apply GlobalTheory.RealZetaProof.realZeta <;> assumption)
