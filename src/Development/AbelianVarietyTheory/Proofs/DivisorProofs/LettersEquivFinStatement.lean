import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LettersEquivFin
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letters_equiv_fin : ∀ (D : D7) (O : Setup D), Nonempty (Fin (D.R.f * O.N) ≃ Pad.Letter O.S.Dw) := by
  first | exact @GlobalTheory.LetterCount.nonempty_equiv_letter | exact GlobalTheory.LetterCount.nonempty_equiv_letter | (intros; apply GlobalTheory.LetterCount.nonempty_equiv_letter <;> assumption)
