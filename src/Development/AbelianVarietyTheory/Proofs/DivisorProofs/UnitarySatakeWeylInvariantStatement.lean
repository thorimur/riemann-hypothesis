import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatake_weylInvariant : Formalism.UG.SatWeyl := by
  first | exact @GlobalTheory.SatakeWeyl.satWeyl | exact GlobalTheory.SatakeWeyl.satWeyl | (intros; apply GlobalTheory.SatakeWeyl.satWeyl <;> assumption)
