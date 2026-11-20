import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelBoundGivesConstantBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradientStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowStatementOfConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosenessStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePartOfHessianCenterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPartOfLowCenterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosePartOfSizeLowCloseStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false

namespace GlobalTheory.RegEst

theorem regSt : Hypotheses2 → HypothesesH → GlobalTheory.Published.DemaillyRegularisation → RegSt := by
  intro h2 hH hD
  have hK := GlobalTheory.T.kernel_statement
  have hC := GlobalTheory.T.kernel_bound_gives_constant_bound h2 hH hD hK
  have hS := GlobalTheory.T.size_statement h2 hH
  have hG := GlobalTheory.T.gradient_statement h2 hH
  have hL := GlobalTheory.T.low_statement_of_constants h2 hH hK hS hC
  have hHs := GlobalTheory.T.hessian_statement hC hL
  have hCl := GlobalTheory.T.closeness_statement h2 hH hK hG
  have hCe := GlobalTheory.T.centre_statement h2 hH
  intro D O hO hN A T H h c
  exact inS_of_parts _ (GlobalTheory.T.curvature_part_of_hessian_center hHs hCe D O hO hN A T H h c) (GlobalTheory.T.boundary_part_of_low_center hL hCe D O hO hN A T H h c)
    (GlobalTheory.T.close_part_of_size_low_close hS hL hCl D O hO hN A T H h c)

end GlobalTheory.RegEst
