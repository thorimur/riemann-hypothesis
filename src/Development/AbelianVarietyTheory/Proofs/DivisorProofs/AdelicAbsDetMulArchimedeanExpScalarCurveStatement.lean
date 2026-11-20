import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAbsDetMulArchimedeanExpScalarCurve
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicAbsDet_mul_archimedeanExpScalarCurve : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (g : GA E a) (t : ℝ),
    absDetA (g * expCurve E a t) = absDetA g * Real.exp (t * (a * Module.finrank ℚ E)) := by
  first | exact @GlobalTheory.HCF.absDetA_mul_expCurve | exact GlobalTheory.HCF.absDetA_mul_expCurve | (intros; apply GlobalTheory.HCF.absDetA_mul_expCurve <;> assumption)
