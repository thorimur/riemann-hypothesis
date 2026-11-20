import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidalSupport_unique_GL : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (s t : Multiset (IrrGL k)), HasSupport x.rep s → HasSupport x.rep t → s = t := by
  first | exact @GlobalTheory.LocGL.SupportUnique.hasSupport_unique | exact GlobalTheory.LocGL.SupportUnique.hasSupport_unique | (intros; apply GlobalTheory.LocGL.SupportUnique.hasSupport_unique <;> assumption)
