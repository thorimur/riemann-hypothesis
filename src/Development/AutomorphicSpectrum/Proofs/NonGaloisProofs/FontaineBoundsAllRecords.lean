import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamAll
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.CompanionTheory.Fontaine

theorem adm7_all : ∀ D : D7, LocalSituation.adm7 D :=
  GlobalTheory.Per.FontaineAll.fontaine_bounds

end GlobalTheory.CompanionTheory.Fontaine
