import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPowerDetAbs_realDiagonal_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  first | exact @GlobalTheory.HalfModTorus.halfMod_torus | exact GlobalTheory.HalfModTorus.halfMod_torus | (intros; apply GlobalTheory.HalfModTorus.halfMod_torus <;> assumption)
