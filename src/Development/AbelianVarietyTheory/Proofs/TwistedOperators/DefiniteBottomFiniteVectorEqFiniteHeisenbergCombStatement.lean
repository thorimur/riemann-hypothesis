import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomFiniteVectorEqFiniteHeisenbergComb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_finiteVector_eq_finite_heisenbergComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO A' WW), (∀ k, (x k).map (infPart D) = 0) ∧
      X.f' t = ∑ k, c k • heisO W.ψ A' WW (x k) X.vac' := by
  first | exact @GlobalTheory.BottomFinComb.finVec_isFinComb | exact GlobalTheory.BottomFinComb.finVec_isFinComb | (intros; apply GlobalTheory.BottomFinComb.finVec_isFinComb <;> assumption)
