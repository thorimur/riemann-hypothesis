import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalConjOfNotGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalOfGoodEmbedding

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdGram

section Pure

open Matrix Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms GlobalTheory.HermFrame GlobalTheory.CurvInterp GlobalTheory.MatDeriv
open scoped ComplexOrder

end Pure

section Obj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.MatDeriv GlobalTheory.GradedNorm Matrix
open scoped ComplexOrder
open GlobalTheory.ShFam.Hor GlobalTheory.HermFrame GlobalTheory.Toroidal

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CurvInterp in

theorem hodgeLocal_all {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    (σ : κ.c.F →+* ℂ) : HodgeLocal x σ := by
  by_cases h : Formalism.L2.PjFree.GoodEmb κ.c σ
  · exact GlobalTheory.CurvInterp.HodgeGood.hodgeLocal_good D A N j S κ s x σ h
  · refine GlobalTheory.CurvInterp.HodgeConj.hodgeLocal_of_conj D A N j S κ s x σ h
      (GlobalTheory.CurvInterp.HodgeGood.hodgeLocal_good D A N j S κ s x _ ?_)
    have h' : ¬ GoodEmb κ.c σ := h
    have h1 : GoodEmb κ.c ((starRingEnd ℂ).comp σ) := by simpa only [goodOf, if_neg h'] using goodEmb_goodOf κ.c σ
    exact h1

end Obj

end GlobalTheory.BdGram
