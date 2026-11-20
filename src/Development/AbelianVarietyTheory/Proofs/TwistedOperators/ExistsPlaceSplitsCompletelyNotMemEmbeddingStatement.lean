import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_splitsCompletely_not_mem_embedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Finset (HeightOneSpectrum (𝓞 F))),
    ∃ v ∉ P, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  first | exact @GlobalTheory.SplitAway.exists_splitsFully_notMem | exact GlobalTheory.SplitAway.exists_splitsFully_notMem | (intros; apply GlobalTheory.SplitAway.exists_splitsFully_notMem <;> assumption)
