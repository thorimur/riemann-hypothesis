import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuasiMeasurePreservingAdelicUnitriangularLeftMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiMeasurePreserving_adelicUnitriangular_left_mul : ∀ (D : D7) (ρ n : ℕ) (μ : Measure (Mx D ρ n)), μ.IsAddHaarMeasure → ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (fun b : Mx D ρ n => u.1.1 ⬝ b) μ μ := by
  first | exact @GlobalTheory.LeftUniQmp.qmp_left_uni | exact GlobalTheory.LeftUniQmp.qmp_left_uni | (intros; apply GlobalTheory.LeftUniQmp.qmp_left_uni <;> assumption)
