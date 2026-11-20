import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGaugeBilinearTermOfTypeNe
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_gaugeBilinearTerm_of_type_ne : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, HasTeich X V g → ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)) := by
  first | exact @GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne | exact GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne | (intros; apply GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne <;> assumption)
