import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaConjInvariant
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_conj_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E), delta (c.map σ) = delta c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap.delta_map <;> assumption)
