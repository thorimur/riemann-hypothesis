import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FurtherLawsOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allSixLaws : Laws ∧ Laws2 ∧ Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  ⟨abelianSchemeLaws_all.1, abelianSchemeLaws_all.2,
    furtherLaws_of_laws abelianSchemeLaws_all.1 twistBaseChange⟩

end GlobalTheory
