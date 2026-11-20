import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesGoodAlmostAllPlaces
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalHermitianFrames_good_almost_all_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), {p | ¬ Good (G.S p)}.Finite := by
  first | exact @GlobalTheory.HL.StdPlace.good_almost_all | exact GlobalTheory.HL.StdPlace.good_almost_all | (intros; apply GlobalTheory.HL.StdPlace.good_almost_all <;> assumption)
