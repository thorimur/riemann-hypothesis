import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmoothKFiniteUnitHighestWeightVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_kFinite_unit_highestWeight_vector : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ w : M.H τ, w ∈ M.sm τ ∧ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ ∧ IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) w := by
  first | exact @GlobalTheory.RealZetaSmoothHi.exists_smooth_highestUnit | exact GlobalTheory.RealZetaSmoothHi.exists_smooth_highestUnit | (intros; apply GlobalTheory.RealZetaSmoothHi.exists_smooth_highestUnit <;> assumption)
