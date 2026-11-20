import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactClopenNhdsOneGLFiniteAdeles
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))), B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  first | exact @GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | exact GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | (intros; apply GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen <;> assumption)
