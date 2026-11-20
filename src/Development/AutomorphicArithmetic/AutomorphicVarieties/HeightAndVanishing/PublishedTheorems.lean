import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.KBridgeOfKPublishedW
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoLitOOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert

open UpperTheory.Top

namespace UpperTheory.V

open UpperTheory.V.Published

structure PublishedTheorems : Prop where
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : GaloisRepReal
  thorne : ThorneAdjoint
  descU : DescentUnitary
  types : TypesNZero
  cyc : CyclicBaseChange
  jl : JacquetLanglands
  adj : AdjointLift
  cube : SymCube
  ind : QuadInduction
  eis : HilbertEisOne
  one : HilbertOne
  kato : Lit.KatoO
  k : KPublishedW

end UpperTheory.V
