import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharFiniteRationalEqExp
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_finite_rational_eq_exp : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : F,
    ψ (pairA F 0 (algebraMap F (Af F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  first | exact @GlobalTheory.StdFinRat.std_fin_rat | exact GlobalTheory.StdFinRat.std_fin_rat | (intros; apply GlobalTheory.StdFinRat.std_fin_rat <;> assumption)
