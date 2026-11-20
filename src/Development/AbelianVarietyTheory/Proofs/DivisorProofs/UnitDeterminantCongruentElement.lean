import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatReflection

theorem latHat_eq_lamHat {D : D7} (V : HSp D) : Formalism.L2.Pj.latHat V = Formalism.L2.NTheta.LamHat V := by
  rw [GlobalTheory.LatDual.lamHat_eq_hat]
  exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1

end GlobalTheory.LatReflection
