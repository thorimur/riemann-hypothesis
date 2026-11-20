import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  first | exact @GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | exact GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | (intros; apply GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO <;> assumption)
