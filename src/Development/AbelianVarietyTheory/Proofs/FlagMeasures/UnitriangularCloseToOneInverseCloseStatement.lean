import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseClose
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_close_to_one_inverse_close : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E), t ∈ L.O → (∀ i j, j < i → M i j = 0) → (∀ i, M i i = 1) → (∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) → ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  first | exact @GlobalTheory.unitriangular_inv_close | exact GlobalTheory.unitriangular_inv_close | (intros; apply GlobalTheory.unitriangular_inv_close <;> assumption)
