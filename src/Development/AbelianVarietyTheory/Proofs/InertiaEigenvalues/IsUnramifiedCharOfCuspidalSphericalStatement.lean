import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedChar_of_cuspidal_spherical : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k), x.IsCusp → IsSpherical x.rep → x.IsUnramChar := by
  first | exact @GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical | exact GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical | (intros; apply GlobalTheory.LocLanglands.isUnramChar_of_isCusp_of_isSpherical <;> assumption)
