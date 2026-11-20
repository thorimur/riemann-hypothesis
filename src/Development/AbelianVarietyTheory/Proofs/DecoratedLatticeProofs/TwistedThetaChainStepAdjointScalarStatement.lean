import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaChain_step_adjoint_scalar : ∀ D : D7, SoftQ D → UpParQ D → UpQ D → QOfVal D → UpVal D → StepExactNS D → LFull D → Restore D → StepLam D := by
  first | exact @GlobalTheory.ChainTw.stepLam_of_ns | exact GlobalTheory.ChainTw.stepLam_of_ns | (intros; apply GlobalTheory.ChainTw.stepLam_of_ns <;> assumption)
