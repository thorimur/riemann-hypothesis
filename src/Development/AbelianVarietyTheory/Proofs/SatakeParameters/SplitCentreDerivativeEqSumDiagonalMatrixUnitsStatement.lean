import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitCentreDerivativeEqSumDiagonalMatrixUnits
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCentreDerivative_eq_sum_diagonalMatrixUnits : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GlobalTheory.ResW.zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i := by
  first | exact @GlobalTheory.ResW.zc_eq_sum_Eop | exact GlobalTheory.ResW.zc_eq_sum_Eop | (intros; apply GlobalTheory.ResW.zc_eq_sum_Eop <;> assumption)
