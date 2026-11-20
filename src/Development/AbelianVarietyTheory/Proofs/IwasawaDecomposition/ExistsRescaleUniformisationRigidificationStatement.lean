import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidification
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_uniformisation_rigidification : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  first | exact @GlobalTheory.RigRescale.exists_rescale_rig | exact GlobalTheory.RigRescale.exists_rescale_rig | (intros; apply GlobalTheory.RigRescale.exists_rescale_rig <;> assumption)
