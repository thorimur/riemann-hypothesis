import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalfStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinitesimalWeightOfDualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatibStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

namespace GlobalTheory

theorem weightParam_of_pin : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  intro hL D P
  exact GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible D P.M P.tp.tup P.H.level (GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half D P.cf P.C P.tp P.chr) (GlobalTheory.T.infinitesimal_weight_of_dual D P.M P.tp.tup P.H)

end GlobalTheory
