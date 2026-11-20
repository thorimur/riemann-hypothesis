import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.DescentTheorem.DescentOf

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.G

namespace UpperTheory.V.Z.Tf.GOne

def NoOther : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∀ D : Pre E n, D.Reg → D.ThetaStable → SplitLike D π → IsOne D π

end UpperTheory.V.Z.Tf.GOne
