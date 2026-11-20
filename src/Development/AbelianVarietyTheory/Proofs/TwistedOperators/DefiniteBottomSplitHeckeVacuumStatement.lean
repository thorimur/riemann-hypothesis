import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitHeckeVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_splitHecke_vacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW), Formalism.L2.NTheta.IsHeckeElt (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) e (ϖ : D.host.E) k α →
      ∃ Δ : Finset (WO (GlobalTheory.Grid.neg A) WW), (∀ u ∈ Δ, u.map (infPart D) = 0) ∧
        X.ω t (1, α) X.vac =
          ((((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW α) : Circle) : ℂ) *
            ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ Δ, heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac := by
  first | exact @GlobalTheory.RowEx.BottomHecke.vacuum_hecke | exact GlobalTheory.RowEx.BottomHecke.vacuum_hecke | (intros; apply GlobalTheory.RowEx.BottomHecke.vacuum_hecke <;> assumption)
