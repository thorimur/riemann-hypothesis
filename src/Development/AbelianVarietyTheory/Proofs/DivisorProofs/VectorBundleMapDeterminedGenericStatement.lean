import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleMapDeterminedGeneric

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_map_determined_generic : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O)
    (F G : Z.X.Modules) (m : ℕ) (a b : F ⟶ G), GlobalTheory.VB.IsVB G m → Z.genRes.map a = Z.genRes.map b → a = b := by
  first | exact @GlobalTheory.MixedLocalChains.hom_ext_of_genRes | exact GlobalTheory.MixedLocalChains.hom_ext_of_genRes | (intros; apply GlobalTheory.MixedLocalChains.hom_ext_of_genRes <;> assumption)
