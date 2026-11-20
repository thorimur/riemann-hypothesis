import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentTangentLetters
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_tangent_letters : ∀ (D : D7) (O : Setup D) (y : Pt O.s), LinearIndependent Qb (fun l : Pad.Letter O.S.Dw => tanOf (y.tan l.1 l.2)) := by
  first | exact @GlobalTheory.FlagFrame.pt_frame_linearIndependent | exact GlobalTheory.FlagFrame.pt_frame_linearIndependent | (intros; apply GlobalTheory.FlagFrame.pt_frame_linearIndependent <;> assumption)
