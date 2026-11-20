import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridModulusExactOrderWitness
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridModulus_exact_order_witness : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), ∀ v ∈ G.pl.S0,
  (∃ m ∈ G.modul, m ∉ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1)) ∧ ∃ m ∈ G.modul, m ∉ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := by
  first | exact @GlobalTheory.ChiGrid.GridData.modul_witness | exact GlobalTheory.ChiGrid.GridData.modul_witness | (intros; apply GlobalTheory.ChiGrid.GridData.modul_witness <;> assumption)
