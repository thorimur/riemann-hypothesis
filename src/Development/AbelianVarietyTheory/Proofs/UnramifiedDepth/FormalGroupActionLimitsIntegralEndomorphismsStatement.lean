import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLimitsIntegralEndomorphisms
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd), EndomorphismLimitIntegral Y := by
  first | exact @GlobalTheory.ActLimit.limit_endomorphisms | exact GlobalTheory.ActLimit.limit_endomorphisms | (intros; apply GlobalTheory.ActLimit.limit_endomorphisms <;> assumption)
