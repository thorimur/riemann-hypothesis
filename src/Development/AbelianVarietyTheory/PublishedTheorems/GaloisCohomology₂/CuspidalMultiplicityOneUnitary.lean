import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CuspidalMultiplicityOneUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π π' : CuspSub E a,
    π.IsUnitary → π'.IsUnitary → CG.mk π = CG.mk π' → π.V = π'.V

end GlobalTheory.Published

end
