import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsGaugeAdjointIntegralEndPairAdd
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGaugeAdjointIntegralEndPair_add : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ M M' N N' : Matrix κ κ C, IsEnd X V M M' → IsEnd X V N N' → IsEnd X V (M + N) (M' + N') := by
  first | exact @GlobalTheory.RowLaw.EndSum.isEnd_add | exact GlobalTheory.RowLaw.EndSum.isEnd_add | (intros; apply GlobalTheory.RowLaw.EndSum.isEnd_add <;> assumption)
