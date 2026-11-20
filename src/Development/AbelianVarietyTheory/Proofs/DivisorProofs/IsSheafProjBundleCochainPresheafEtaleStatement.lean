import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSheafProjBundleCochainPresheafEtale
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ), Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  first | (exact @GlobalTheory.EtC.cotPre_isSheaf) | (exact GlobalTheory.EtC.cotPre_isSheaf) | (intros; apply GlobalTheory.EtC.cotPre_isSheaf  <;> assumption)
