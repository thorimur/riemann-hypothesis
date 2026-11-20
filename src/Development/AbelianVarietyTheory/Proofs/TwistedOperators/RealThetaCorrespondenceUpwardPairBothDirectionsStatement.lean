import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirections
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (S S' : SPar) (aS aT : ℚ), UpPair t S S' aS aT → (∀ (τ : D.what₂.Tau) (V W : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ToSource τ V W aS aT S S' ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ZetaSource τ V W aS aT S S') ∧ ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → GlobalTheory.PairLift.RulePar X S S' aS aT ∧ GlobalTheory.PairLift.RulePar X S' S aT aS := by
  first | exact @GlobalTheory.EvenOnto.upPair_arch | exact GlobalTheory.EvenOnto.upPair_arch | (intros; apply GlobalTheory.EvenOnto.upPair_arch <;> assumption)
