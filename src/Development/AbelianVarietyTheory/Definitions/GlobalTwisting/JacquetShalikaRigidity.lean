import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DiscreteSeriesCoefficientsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

namespace GlobalTheory.Fc.S0

structure Hypotheses1 : Prop extends ArithmeticGeometryHyps where
  hilbertClassFieldJ : GlobalTheory.Published.HilbertClassFieldJ
  siegelWeilUnitarySchrodinger : GlobalTheory.Published.SiegelWeilUnitarySchrodinger
  localTateDualityK : Formalism.GaloisCohomology.LocalTateDualityK
  localEulerCharK : Formalism.GaloisCohomology.LocalEulerCharK
  localFinitenessK : Formalism.GaloisCohomology.LocalFinitenessK
  bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral
  jacquetShalikaRigidity : GlobalTheory.Published.JacquetShalikaRigidity

end GlobalTheory.Fc.S0
