import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreQuotientLValues
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistEulerFactors_restore_quotientLValues : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, (∀ H H₀, IsHval c (c.S : Set _) k H → IsHval c w.S₀ k H₀ → H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) ∧ ∃ H₀, H₀ ≠ 0 ∧ IsHval c w.S₀ k H₀ := by
  first | exact @GlobalTheory.ChainTw.EulerAtTwist.restore_hval | exact GlobalTheory.ChainTw.EulerAtTwist.restore_hval | (intros; apply GlobalTheory.ChainTw.EulerAtTwist.restore_hval <;> assumption)
