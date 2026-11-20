import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingNegativeVacuumDefiniteBottom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_fixing_negative_vacuum_definite_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧
      ∀ k ∈ U, k ∈ GfC A → X.ω t (k, 1) X.vac = X.vac := by
  first | exact @GlobalTheory.VacFixNeg.exists_open_fix_vac_neg | exact GlobalTheory.VacFixNeg.exists_open_fix_vac_neg | (intros; apply GlobalTheory.VacFixNeg.exists_open_fix_vac_neg <;> assumption)
