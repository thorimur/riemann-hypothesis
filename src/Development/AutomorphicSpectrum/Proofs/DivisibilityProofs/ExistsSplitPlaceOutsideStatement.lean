import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsSplitPlaceOutside
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_place_outside : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois ℚ E] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)), ∃ v ∉ S, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RT.exists_splitsFully_notMem | exact GlobalTheory.CompanionTheory.Ar.RT.exists_splitsFully_notMem | (intros; apply GlobalTheory.CompanionTheory.Ar.RT.exists_splitsFully_notMem <;> assumption)
