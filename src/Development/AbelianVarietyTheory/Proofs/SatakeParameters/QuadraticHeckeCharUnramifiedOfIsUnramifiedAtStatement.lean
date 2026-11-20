import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | exact GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | (intros; apply GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt <;> assumption)
