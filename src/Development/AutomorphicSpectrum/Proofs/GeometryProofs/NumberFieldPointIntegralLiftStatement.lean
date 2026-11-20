import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_point_integral_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : FiniteDimensional ℚ c.F) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (f : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f → ∃ yt : Sp (𝓞 F) ⟶ Y.X, spMap (algebraMap (𝓞 F) F) ≫ yt = y ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.model_point_extends_to_integers | exact GlobalTheory.CompanionTheory.Ar.model_point_extends_to_integers | (intros; apply GlobalTheory.CompanionTheory.Ar.model_point_extends_to_integers <;> assumption)
