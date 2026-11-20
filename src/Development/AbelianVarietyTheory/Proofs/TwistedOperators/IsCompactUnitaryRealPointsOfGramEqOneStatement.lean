import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryRealPoints_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  first | exact @GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | exact GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | (intros; apply GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one <;> assumption)
