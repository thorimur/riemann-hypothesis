import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionLeftExactFunctorKernelSquareMatrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_left_exact_functor_kernel_square_matrix : KernelRep := by
  first | exact @GlobalTheory.KRep.kernelRep | exact GlobalTheory.KRep.kernelRep | (intros; apply GlobalTheory.KRep.kernelRep <;> assumption)
