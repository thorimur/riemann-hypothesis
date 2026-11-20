import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafComplex_mappingCone_acyclic_of_quasiIso : ∀ (R : Type) [CommRing R] {C J : Cx R} (u : C ⟶ J) [QuasiIso u], (mappingCone u).Acyclic := by
  first | exact @GlobalTheory.EtC.mappingCone_acyclic | exact GlobalTheory.EtC.mappingCone_acyclic | (intros; apply GlobalTheory.EtC.mappingCone_acyclic <;> assumption)
