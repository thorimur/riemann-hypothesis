import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTrivialBoundInertPlaceUnitarisableSpherica
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeTrivialBound_inertPlace_unitarisable_spherical : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert := by
  first | exact @GlobalTheory.SatBoundInert.satakeBoundInert | exact GlobalTheory.SatBoundInert.satakeBoundInert | (intros; apply GlobalTheory.SatBoundInert.satakeBoundInert <;> assumption)
