import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RangeRes
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_cm_character_injective : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ η : QCM F Ω → (G F Ω →* ℤˣ), Function.Injective η ∧ ∀ Q, (η Q).ker = (res F Ω ↥Q.K).range ∧ IsOpen ((η Q).ker : Set (G F Ω)) := by
  first | exact @GlobalTheory.RealGal.SignChar.main | exact GlobalTheory.RealGal.SignChar.main | (intros; apply GlobalTheory.RealGal.SignChar.main <;> assumption)
