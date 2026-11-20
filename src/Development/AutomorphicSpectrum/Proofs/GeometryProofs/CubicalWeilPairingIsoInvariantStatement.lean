import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalWeilPairingIsoInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_weil_pairing_iso_invariant : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂), LBIso L₁.L L₂.L → ∀ (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ), CubWeil c₁ N x y ζ → CubWeil c₂ N x y ζ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso | exact GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso | (intros; apply GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso <;> assumption)
