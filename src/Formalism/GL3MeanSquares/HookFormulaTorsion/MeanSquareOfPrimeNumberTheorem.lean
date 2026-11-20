import Formalism.GL3MeanSquares.PrimePairOfPrimeNumberTheoremInProgressions
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqFinal

noncomputable section

namespace Formalism.HermitianLattices.PrimeNumberTheoremConsequences

theorem PNTAPRelW_iff_ext : PNTAPRelW ↔ Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW := Iff.rfl

theorem mean_square_of_prime_number_theorem : MeanSquareFromPNT := fun hP =>
  Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.mean_square_of_pnt_progressions (PNTAPRelW_iff_ext.1 hP)

end Formalism.HermitianLattices.PrimeNumberTheoremConsequences
