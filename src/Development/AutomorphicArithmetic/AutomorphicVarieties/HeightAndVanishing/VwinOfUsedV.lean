import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.EndoscopicGroupCriteria.UnitaryUp3OfUpAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN

open UpperTheory.Top

namespace UpperTheory.V

structure UsedV : Prop where
  desc : Z.Desc.DescWeak
  desc2 : Z.Bc.ImagQuadraticDescentGL2
  lift2 : Z.Bc.QuadBC2
  lift3 : Z.Sym.Q.Up3
  ind : Z.Bc.IndC
  kato : Z.Kato.KatoTwo

end UpperTheory.V
