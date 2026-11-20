import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorOrderFiniteIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_order_finite_integers : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), Module.Finite ℤ (orderC c) := by
  first | exact @GlobalTheory.LatModel.finite_int_orderC | exact GlobalTheory.LatModel.finite_int_orderC | (intros; apply GlobalTheory.LatModel.finite_int_orderC <;> assumption)
