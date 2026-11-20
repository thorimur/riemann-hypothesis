import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.IntSOfSIntFin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.JSIntFin

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.NVHTop

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem intS : S0.IntSStatement :=
  S0.IntS.intS_of_sIntFin (Mult1.S0.sIntFin Mult1.multiplicity_one_hypotheses_hold)

end ReciprocityTheory.ChartRestriction.DS.Lap.NVHTop
