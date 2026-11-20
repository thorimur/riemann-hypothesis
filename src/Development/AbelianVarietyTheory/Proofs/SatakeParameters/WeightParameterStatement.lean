import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightParameter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_parameter : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  first | exact @GlobalTheory.weightParam_of_pin | exact GlobalTheory.weightParam_of_pin | (intros; apply GlobalTheory.weightParam_of_pin <;> assumption)
