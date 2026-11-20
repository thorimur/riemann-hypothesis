import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedIsHermitianLogOfPosDef
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_isHermitianLogOfPosDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by
  first | exact @GlobalTheory.ClassFin.isClosed_isLog | exact GlobalTheory.ClassFin.isClosed_isLog | (intros; apply GlobalTheory.ClassFin.isClosed_isLog <;> assumption)
