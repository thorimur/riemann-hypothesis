import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusLiftLemmasOfAdmitted
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremC_of_admitted_inputs :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (CR CA CB CK : ℝ), LiftingTheory.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F →
      ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F → CrystallineLiftingBounds.adm22 D HW F → InvariantsGenerators.LitFont D HW F →
      RamifiedCoefficientChains.Stmt D HW F Cm 25 CR CA CB CK :=
  fun D HW F Cm CR CA CB CK h23 hC4 hHerr a22 hFont =>
    Formalism.MainNotions.RamifiedCoefficientChains.Asm.theorem_of_literature_hypotheses D HW F Cm CR CA CB CK h23 hC4 hHerr a22 hFont

end GlobalTheory
