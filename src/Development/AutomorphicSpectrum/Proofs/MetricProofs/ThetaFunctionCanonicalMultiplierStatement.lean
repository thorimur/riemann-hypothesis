import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionCanonicalMultiplier
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_canonical_multiplier : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  first | exact @GlobalTheory.CompanionTheory.CanThLine.level_one_line | exact GlobalTheory.CompanionTheory.CanThLine.level_one_line | (intros; apply GlobalTheory.CompanionTheory.CanThLine.level_one_line <;> assumption)
