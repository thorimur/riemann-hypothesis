import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumeOfBallBound
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_of_ball_bound : VolBall := by
  first | exact @GlobalTheory.SepReal.volBall | exact GlobalTheory.SepReal.volBall | (intros; apply GlobalTheory.SepReal.volBall <;> assumption)
