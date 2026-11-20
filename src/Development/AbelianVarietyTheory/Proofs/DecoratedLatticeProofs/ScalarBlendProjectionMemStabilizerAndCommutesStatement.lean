import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarBlendProjectionMemStabilizerAndCommutes
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarBlend_projection_mem_stabilizer_and_commutes : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (h : X.B.I.Gf), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) → GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u → X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c → h ∈ Hfin X u ∧ ∀ h' ∈ Hfin X u, h * h' = h' * h := by
  first | exact @GlobalTheory.ScalW.hMat_mem_hfin_comm | exact GlobalTheory.ScalW.hMat_mem_hfin_comm | (intros; apply GlobalTheory.ScalW.hMat_mem_hfin_comm <;> assumption)
