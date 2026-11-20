import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weak_neron_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  first | exact @GlobalTheory.SS.WeakNeronEx.exists_weakNeron | exact GlobalTheory.SS.WeakNeronEx.exists_weakNeron | (intros; apply GlobalTheory.SS.WeakNeronEx.exists_weakNeron <;> assumption)
