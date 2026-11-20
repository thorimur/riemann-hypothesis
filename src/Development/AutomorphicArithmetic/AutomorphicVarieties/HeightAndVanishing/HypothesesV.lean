import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.KBridgeOfKPublished

open UpperTheory.Top

namespace UpperTheory.V

open UpperTheory.V.Published

structure HypothesesV : Prop where
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
  adj : AdjointLift
  cube : SymCube
  ind : QuadInduction
  eis : HilbertEisOne
  one : HilbertOne
  kato : Kato
  k : KPublished

end UpperTheory.V
