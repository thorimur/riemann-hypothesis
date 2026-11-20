import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ActionConvergesLadicCauchyAndStar
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actionConverges_ladic_cauchy_and_star : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (a : ℕ → O), (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ActCv Y a ∧ ActCv Y (fun n => star (a n)) := by
  first | exact @GlobalTheory.ActionLimit.main | exact GlobalTheory.ActionLimit.main | (intros; apply GlobalTheory.ActionLimit.main <;> assumption)
