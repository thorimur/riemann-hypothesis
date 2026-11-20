import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneLabels_all_places_of_fixed_and_conj : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), LabTrue D T → LabConj D T → GlobalTheory.PendOf.LabAll D T := by
  first | exact @GlobalTheory.LabAllOf.labAll_of_labTrue_labConj | exact GlobalTheory.LabAllOf.labAll_of_labTrue_labConj | (intros; apply GlobalTheory.LabAllOf.labAll_of_labTrue_labConj <;> assumption)
