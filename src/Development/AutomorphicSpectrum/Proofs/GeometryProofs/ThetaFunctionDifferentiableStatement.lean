import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionDifferentiable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_differentiable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → Differentiable ℂ θ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.isFn_differentiable | exact GlobalTheory.CompanionTheory.Ar.Sl.isFn_differentiable | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.isFn_differentiable <;> assumption)
