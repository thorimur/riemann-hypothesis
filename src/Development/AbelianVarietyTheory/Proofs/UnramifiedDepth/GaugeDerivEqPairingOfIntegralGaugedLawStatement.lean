import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLaw
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.CEqSt H := by
  first | exact @GlobalTheory.RowLaw.cEqSt_of_rLaw | exact GlobalTheory.RowLaw.cEqSt_of_rLaw | (intros; apply GlobalTheory.RowLaw.cEqSt_of_rLaw <;> assumption)
