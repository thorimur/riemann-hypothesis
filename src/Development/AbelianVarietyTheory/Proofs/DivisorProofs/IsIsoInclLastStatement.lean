import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLast
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_incl_last' : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι), IsIso (incl ι N τ (Fin.last N)) := by
  first | exact @GlobalTheory.FlagZ.Univ.isIso_incl_last | exact GlobalTheory.FlagZ.Univ.isIso_incl_last | (intros; apply GlobalTheory.FlagZ.Univ.isIso_incl_last <;> assumption)
