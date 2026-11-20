import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSegmentRep_length_one_unramified : LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL k), IsLSeg Δ y.rep → IsSpherical y.rep → Δ.len = 1 ∧ Δ.first.IsUnramChar := by
  first | exact @GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | exact GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | (intros; apply GlobalTheory.SphSeg.len_eq_one_and_isUnramChar <;> assumption)
