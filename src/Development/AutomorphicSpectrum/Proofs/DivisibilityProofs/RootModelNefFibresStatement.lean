import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelNefFibres
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_nef_fibres : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg | exact GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg <;> assumption)
