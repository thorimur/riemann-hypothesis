import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.ThetaExh.LocOfPt N A i := by
  first | exact @GlobalTheory.RowTie.locOfPt_of_splitBC | exact GlobalTheory.RowTie.locOfPt_of_splitBC | (intros; apply GlobalTheory.RowTie.locOfPt_of_splitBC <;> assumption)
