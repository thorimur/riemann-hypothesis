import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

open NumberField GlobalTheory.CuspRep Formalism.BasicNotions Formalism.MainNotions.N

def UpperTheory.V.Ws.CuspidalRankFourRegularAlgebraic {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] (π : CuspSub L 4) : Prop := (CG.mk π).IsRegAlg
