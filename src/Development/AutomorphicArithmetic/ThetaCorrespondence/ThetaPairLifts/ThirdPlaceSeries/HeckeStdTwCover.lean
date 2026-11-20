import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.NPin
theorem heckeStdTw_cover_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), HeckeStdTw P.H.cover.B :=
  fun _ D P =>
    Formalism.L2.heckeStd_of_plain P.H.cover GlobalTheory.HeckeStdFacts.heckeStdPlain P.H.hecke (GlobalTheory.SplitConjPlace.splitEx_all D)
      (Formalism.L2.genOutBad_of P.H.cover)
end GlobalTheory.NPin
end
