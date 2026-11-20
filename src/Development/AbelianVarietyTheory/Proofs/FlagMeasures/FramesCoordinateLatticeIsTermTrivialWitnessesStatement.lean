import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCoordinateLatticeIsTermTrivialWitnesses
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framesCoordinateLattice_isTerm_trivialWitnesses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 := by
  first | exact @GlobalTheory.HL.CoordGood.main | exact GlobalTheory.HL.CoordGood.main | (intros; apply GlobalTheory.HL.CoordGood.main <;> assumption)
