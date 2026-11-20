import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseUnitaryRealPointsAlgebraicEntries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_unitaryRealPoints_algebraicEntries : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ V : HSp D, Dense {g : GinfC V | ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)} := by
  first | exact @GlobalTheory.RealAlgDense.dense_alg | exact GlobalTheory.RealAlgDense.dense_alg | (intros; apply GlobalTheory.RealAlgDense.dense_alg <;> assumption)
