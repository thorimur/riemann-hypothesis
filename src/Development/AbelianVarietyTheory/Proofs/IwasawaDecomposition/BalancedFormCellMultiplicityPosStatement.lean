import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPos
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedFormCellMultiplicity_pos : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m : ℕ} (δ : Fin m → balForms bar X), 0 < cellMult bar δ := by
  first | exact @GlobalTheory.PolFan.cellMult_pos | exact GlobalTheory.PolFan.cellMult_pos | (intros; apply GlobalTheory.PolFan.cellMult_pos <;> assumption)
