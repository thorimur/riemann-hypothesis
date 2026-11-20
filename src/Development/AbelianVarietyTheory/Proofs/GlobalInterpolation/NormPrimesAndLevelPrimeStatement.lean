import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_primes_and_level_prime : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → NormPrimes ∧ LevelPrime := by
  first | exact @GlobalTheory.EX.normPrimes_and_levelPrime | exact GlobalTheory.EX.normPrimes_and_levelPrime | (intros; apply GlobalTheory.EX.normPrimes_and_levelPrime <;> assumption)
