import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_factor_of_spherical_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsSubquotient π (prodIrr x hd) → IsSpherical π → ∀ a, IsSpherical (x a).rep := by
  first | exact @GlobalTheory.LocLanglands.SphFac.isSpherical_factor | exact GlobalTheory.LocLanglands.SphFac.isSpherical_factor | (intros; apply GlobalTheory.LocLanglands.SphFac.isSpherical_factor <;> assumption)
