import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.GalCut7

noncomputable section

namespace GlobalTheory.GalCut7.IwahoriTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut.SsTwist Polynomial UpperTheory.V UpperTheory.V.Af

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : Formalism.ConjugateSelfDual.IsPlaceOver A w}

theorem monodromy_vanishes_weilTwist_iff (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) : (x.lpTwist ξ hξ).mono0 ↔ x.mono0 := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff]
  rfl

theorem charPol_lpTwist_iff (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (g : Weil h) :
    (x.lpTwist ξ hξ).charPol g = (y.lpTwist ξ hξ).charPol g ↔ x.charPol g = y.charPol g := by
  rw [charPol_lpTwist, charPol_lpTwist]
  exact ⟨scaleRoots_cancel (Units.ne_zero _), fun e => by rw [e]⟩

end GlobalTheory.GalCut7.IwahoriTwist

end
