import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.Normed.Ring.Ultra

namespace GlobalTheory.AdicNatCastNorm

theorem norm_natCast_adicCompletion_le_one {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ) :
    ‖(↑n : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)‖ ≤ (1 : ℝ) :=
  IsUltrametricDist.norm_natCast_le_one _ n

end GlobalTheory.AdicNatCastNorm
