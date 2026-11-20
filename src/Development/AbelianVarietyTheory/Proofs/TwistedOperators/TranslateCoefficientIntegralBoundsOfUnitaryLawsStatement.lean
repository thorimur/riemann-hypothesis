import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientIntegralBoundsOfUnitaryLaws
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translateCoefficientIntegralBounds_of_unitary_laws : EmbLaws → Boost → PowInt → DecPow → IntBounds := by
  first | exact @GlobalTheory.SepReal.intBounds_main | exact GlobalTheory.SepReal.intBounds_main | (intros; apply GlobalTheory.SepReal.intBounds_main <;> assumption)
