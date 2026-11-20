import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftOntoAll
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_onto_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  first | exact @GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems_and_hecke | exact GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems_and_hecke | (intros; apply GlobalTheory.ChainOnto.ontoAll_of_classicalTheorems_and_hecke <;> assumption)
