import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ}, IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) := by
  first | exact @GlobalTheory.FinValAlg.finite_values_isAlgebraic | exact GlobalTheory.FinValAlg.finite_values_isAlgebraic | (intros; apply GlobalTheory.FinValAlg.finite_values_isAlgebraic <;> assumption)
