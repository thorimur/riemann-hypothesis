import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProved
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PropZ_proved : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | exact GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds <;> assumption)
