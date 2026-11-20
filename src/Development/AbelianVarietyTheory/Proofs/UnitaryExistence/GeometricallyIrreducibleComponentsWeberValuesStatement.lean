import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValues
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIrreducible_components_weberValues : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l' : Level Q.H) (Xo' : Moduli (Q.Dw j) l') (c' : Coeff l') (n : ℕ), 0 < n → l'.M' ∣ n → (WeberIn Q.H c'.F n ∨ CurveOver Q.H c'.F n) → FnAlgClosed Xo' c' := by
  first | exact @GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn | exact GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn | (intros; apply GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn <;> assumption)
