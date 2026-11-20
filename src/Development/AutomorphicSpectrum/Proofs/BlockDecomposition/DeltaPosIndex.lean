import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex
import Formalism.LocalRingCardinality.DataHost
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin

theorem delta_pos_index : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (c : Matrix (Fin n) (Fin n) E),
    delta c ≠ 0 :=
  fun _ _ _ _ c => GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_ne_zero c

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin
