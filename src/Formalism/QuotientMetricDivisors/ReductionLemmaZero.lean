import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaSecond
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionSecondStep
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.VwEqZeroOfNotMem
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionThirdStepMean
import Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails

namespace Formalism.DivisionValues

theorem reduction_lemma_zero : GramDeterminantQuotientMetric := gram_determinant_quotient_metric
theorem lemmaRb : LemmaRb := reduction_lemma_second
theorem specDet : SpecDet := spectral_determinant_formula
theorem stepB : StepB := reduction_second_step
theorem stepA : StepA := reduction_first_step
theorem stepC : StepC := reduction_third_step

theorem interlace : Formalism.LatticeIndexTer.Interlace := Formalism.LatticeIndexTer.sumInterlacedBound

end Formalism.DivisionValues
