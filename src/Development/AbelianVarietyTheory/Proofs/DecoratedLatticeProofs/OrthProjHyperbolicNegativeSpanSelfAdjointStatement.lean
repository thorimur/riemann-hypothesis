import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanSelfAdjoint
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthProjHyperbolicNegativeSpan_selfAdjoint : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x y : VA X.B.I), hA X.B.I (GlobalTheory.ScalW.prj X u x) y = hA X.B.I x (GlobalTheory.ScalW.prj X u y) := by
  first | exact @GlobalTheory.ScalW.prj_selfAdjoint | exact GlobalTheory.ScalW.prj_selfAdjoint | (intros; apply GlobalTheory.ScalW.prj_selfAdjoint <;> assumption)
