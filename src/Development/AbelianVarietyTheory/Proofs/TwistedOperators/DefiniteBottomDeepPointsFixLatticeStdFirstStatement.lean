import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomDeepPointsFixLatticeStdFirst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_deepPoints_fix_lattice_stdFirst : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧ ∀ k ∈ U, k ∈ GfC A →
      (∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k) 1 u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)) ∧
      ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
          (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ 1⁻¹ x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
  first | exact @GlobalTheory.StdFstFix.stdFst_fixed | exact GlobalTheory.StdFstFix.stdFst_fixed | (intros; apply GlobalTheory.StdFstFix.stdFst_fixed <;> assumption)
