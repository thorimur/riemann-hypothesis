import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerFramesCoordinateLatticeGoodPlace
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_framesCoordinateLattice_goodPlace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → S.a = 0 → ∀ d₀, S.IsTermW d₀ (coordLat S) 1 1 → S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 := by
  first | exact @GlobalTheory.HL.StdStab.stab_coordLat | exact GlobalTheory.HL.StdStab.stab_coordLat | (intros; apply GlobalTheory.HL.StdStab.stab_coordLat <;> assumption)
