import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainLevelIntegralRealZetaOfTwistedTransformLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainLevelIntegralRealZeta_of_twisted_transform_laws : ∀ D : D7, LevelLawQ D → LevInt D := by
  first | exact @GlobalTheory.ChainTw.LevIntProof.levInt | exact GlobalTheory.ChainTw.LevIntProof.levInt | (intros; apply GlobalTheory.ChainTw.LevIntProof.levInt <;> assumption)
