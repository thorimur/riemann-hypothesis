import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoTrivialProjBundleProdFibre
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_trivialProjBundle_prod_fibre : ∀ (q N : ℕ) (F : PSh), Inv q (disc.obj F) → ∃ θ : disc.obj F ⨯ fibQ q N ≅ pullback (trivV N (disc.obj F)) (PGL.pr N), θ.hom ≫ pullback.fst _ _ = prod.fst ∧ θ.hom ≫ pullback.snd _ _ ≫ PGL.line N = prod.snd ≫ lineQ q N := by
  first | (exact @GlobalTheory.EtC.trivProj_iso) | (exact GlobalTheory.EtC.trivProj_iso) | (intros; apply GlobalTheory.EtC.trivProj_iso <;> assumption)
