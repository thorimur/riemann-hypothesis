import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i))) (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'), ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  first | exact @GlobalTheory.CoreVacRe.vacExists_reLat | exact GlobalTheory.CoreVacRe.vacExists_reLat | (intros; apply GlobalTheory.CoreVacRe.vacExists_reLat <;> assumption)
