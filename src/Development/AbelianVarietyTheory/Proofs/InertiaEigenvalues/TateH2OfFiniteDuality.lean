import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem tateH2_of_finite_duality : ∀ (D : Formalism.BasicNotions.D7), adm2 D → adm3 D :=
  fun D h => GlobalTheory.TateTop.tate_h2_of_local_duality h D

end GlobalTheory.Cyc
