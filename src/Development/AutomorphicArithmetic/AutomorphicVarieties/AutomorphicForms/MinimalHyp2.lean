import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

namespace UpperTheory.V.Af

open UpperTheory.V.Published

structure MinimalHyp2 : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  cohC : ClozelCohC
  cohR : ClozelCohR
  conjC : ClozelConjC
  conjR : ClozelConjR
  borelC : BorelInjC
  borelR : BorelInjR
  galR : GaloisRepReal
  smoR : StrongMultOneReal
  bc : QuadBaseChange
  thorne : ThorneAdjoint
  descU : DescentUnitary
  types : TypesNZero
  sign : SignCsd
  cyc : CyclicBaseChange
  jl : JacquetLanglands
  finR : FormsFiniteReal

end UpperTheory.V.Af
