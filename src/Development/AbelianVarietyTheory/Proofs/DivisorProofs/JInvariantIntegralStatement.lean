import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JInvariantIntegral

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.j_invariant_integral : ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    IsIntegral ℤ (1728 * Λ.g₂ ^ 3 / latDisc Λ) := by
  first | exact @GlobalTheory.isIntegral_j_of_isIntLattice | exact GlobalTheory.isIntegral_j_of_isIntLattice | (intros; apply GlobalTheory.isIntegral_j_of_isIntLattice <;> assumption)
