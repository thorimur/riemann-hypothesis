import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_multiplicativeGroup_sections_units : ∀ U : Scheme.{0}, Function.Bijective (ofRings.sec unitsF U) := by
  first | (exact @GlobalTheory.EtC.GmSec.gm_sec_bijective) | (exact GlobalTheory.EtC.GmSec.gm_sec_bijective) | (intros; apply GlobalTheory.EtC.GmSec.gm_sec_bijective  <;> assumption)
