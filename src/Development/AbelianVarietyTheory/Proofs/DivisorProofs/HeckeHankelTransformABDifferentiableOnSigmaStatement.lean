import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABDifferentiableOnSigma
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_differentiableOn | exact GlobalTheory.HeckeTwo.hTransAB_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.hTransAB_differentiableOn <;> assumption)
