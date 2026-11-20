import Formalism.PeriodIntegrals.HeisDefs
import Mathlib.Analysis.CStarAlgebra.Classes

open MeasureTheory

namespace PI.NormPullGW

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

instance haarIJ : (volume : Measure (I → J → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : I => (volume : Measure (J → ℂ)))

instance haarTIJ : (volume : Measure (T → I → J → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : T => (volume : Measure (I → J → ℂ)))

noncomputable def phi (A : ℝ) (F : (T → I → J → ℂ) → ℂ) (z : T → I → J → ℂ) : ℝ :=
  ‖F z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re)

end PI.NormPullGW
