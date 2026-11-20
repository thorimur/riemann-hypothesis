import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorCommutesInfiniteGl
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_operator_commutes_infinite_gl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    ∀ y : GL (Fin a) (Cinf E),
      GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt | exact GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt | (intros; apply GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt <;> assumption)
