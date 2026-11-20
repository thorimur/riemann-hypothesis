import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Lit1

def CuspidalMultiplicityOneLit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), 1 ≤ n →
    ∀ π : CuspSub E n, π.IsUnitary → {π' : CuspSub E n | π'.Iso π}.Subsingleton

end PositivityTheory.Lit1

end
