import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_lift_exists : ∀ (ι : Type) [Fintype ι] (N : ℕ) (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N), ∃ g', Lifts g fl' g' := by
  first | exact @GlobalTheory.FlagZ.Univ.exists_lifts | exact GlobalTheory.FlagZ.Univ.exists_lifts | (intros; apply GlobalTheory.FlagZ.Univ.exists_lifts <;> assumption)
