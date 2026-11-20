import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarAdelicUpperUnitriangularEntryTranslateInvari
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_adelicUpperUnitriangular_entry_translate_invariant : ∀ (D : D7) (ρ : ℕ) (ν : Measure (UX D ρ)), ν.IsHaarMeasure → Measurable (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ∧ IsFiniteMeasureOnCompacts (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν) ∧ ∀ t : Mx D ρ ρ, (∀ i j, ¬ i < j → t i j = 0) → Measure.map (fun x => x + t) (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν) = Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) ν := by
  first | exact @GlobalTheory.UnitTransl.haar_val_add_invariant | exact GlobalTheory.UnitTransl.haar_val_add_invariant | (intros; apply GlobalTheory.UnitTransl.haar_val_add_invariant <;> assumption)
