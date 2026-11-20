import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRestrictScalarsHomMaximalRealSubfield

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_restrictScalarsHom_maximalRealSubfield : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω],
    Continuous (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) : G E Ω →* G (maximalRealSubfield E) Ω) := by
  first | exact @GlobalTheory.restrictScalarsHom_maximalRealSubfield_continuous | exact GlobalTheory.restrictScalarsHom_maximalRealSubfield_continuous | (intros; apply GlobalTheory.restrictScalarsHom_maximalRealSubfield_continuous <;> assumption)
