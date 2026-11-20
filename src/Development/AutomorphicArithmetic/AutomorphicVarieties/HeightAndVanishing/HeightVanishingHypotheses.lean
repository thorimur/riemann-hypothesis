import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.UnitaryDescent.DescentUnitaryOfUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DiscreteGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoLitOOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinLit
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Thorne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.TyDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift

open UpperTheory.Top

namespace UpperTheory.V

open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV

structure HeightVanishingHypotheses : Prop where
  thorne : ThorneLit
  desc : NTDescentU
  types : Ty.ShottonTypes
  cyc : UpperTheory.CBC.LitCBC2
  jl : GlobalJL
  sq : SymSqQ
  cube : SymCubeQ
  arthurClozelBaseChange : ArthurClozelDescent
  henniart : Henniart4
  kisin : KisinLit
  kato : KatoLitO

end UpperTheory.V
