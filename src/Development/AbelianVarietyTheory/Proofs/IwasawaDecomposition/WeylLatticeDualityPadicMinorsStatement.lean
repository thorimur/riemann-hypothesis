import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualityPadicMinors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lattice_duality_padic_minors : WeylLatticeDuality.Stmt := by
  first | exact @GlobalTheory.WeylLatDualPf.stmt_holds | exact GlobalTheory.WeylLatDualPf.stmt_holds | (intros; apply GlobalTheory.WeylLatDualPf.stmt_holds <;> assumption)
