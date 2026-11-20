import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectPadicOfComplex
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_padic_of_complex : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ) (s : ℂ → ℂ), (∀ j, AlgEnt (f j)) → AlgEnt s → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0 → GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  first | exact @GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | exact GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero | (intros; apply GlobalTheory.FrobStickMap.defect_ser1_eq_zero_of_defect_tay_eq_zero <;> assumption)
