import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodPlaceGramInvariantMinorsValuationZero
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlace_gramInvariant_minors_valuation_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → vE L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0 := by
  first | exact @GlobalTheory.HL.StdPlace.vE_G_D_eq_zero | exact GlobalTheory.HL.StdPlace.vE_G_D_eq_zero | (intros; apply GlobalTheory.HL.StdPlace.vE_G_D_eq_zero <;> assumption)
