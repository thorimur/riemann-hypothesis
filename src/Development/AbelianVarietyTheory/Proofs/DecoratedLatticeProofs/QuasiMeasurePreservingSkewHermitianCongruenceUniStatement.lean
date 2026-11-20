import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuasiMeasurePreservingSkewHermitianCongruenceUni
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiMeasurePreserving_skewHermitianCongruence_unitriangular : ∀ (D : D7) (ρ : ℕ) (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure → ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (skewConj u.1.1) lC lC := by
  first | exact @GlobalTheory.Unf.SkewConjQmp.quasiMeasurePreserving_skewConj | exact GlobalTheory.Unf.SkewConjQmp.quasiMeasurePreserving_skewConj | (intros; apply GlobalTheory.Unf.SkewConjQmp.quasiMeasurePreserving_skewConj <;> assumption)
