import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_smooth_projective_variety_properties : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y) (D : ℕ) [SmoothOfRelativeDimension D p], IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → GeometricallyConnected p → IsIntegral X ∧ IsLocallyNoetherian X ∧ SmoothOfRelativeDimension D q ∧ IsProjOver q ∧ Function.Surjective π := by
  first | exact @GlobalTheory.BaseChangeVariety.baseChange_props | exact GlobalTheory.BaseChangeVariety.baseChange_props | (intros; apply GlobalTheory.BaseChangeVariety.baseChange_props <;> assumption)
