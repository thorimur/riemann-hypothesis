import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueHomZmodAtTypePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residueHom_zmod_at_typePlace : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    Nonempty (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)) := by
  first | exact @GlobalTheory.TypePlaceResidue.residueHom_zmod | exact GlobalTheory.TypePlaceResidue.residueHom_zmod | (intros; apply GlobalTheory.TypePlaceResidue.residueHom_zmod <;> assumption)
