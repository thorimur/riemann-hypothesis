import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntCastIsUnitCompletionAlmostAllPlaces
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intCast_isUnit_completion_almost_all_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (D : ℤ), D ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (D : (A.loc p).Fp)}.Finite := by
  first | exact @GlobalTheory.HL.PlacesInt.intCast_isUnit_almost_all | exact GlobalTheory.HL.PlacesInt.intCast_isUnit_almost_all | (intros; apply GlobalTheory.HL.PlacesInt.intCast_isUnit_almost_all <;> assumption)
