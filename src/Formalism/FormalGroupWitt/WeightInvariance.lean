import Formalism.FormalGroupWitt.FormalGroupWittProofs.AdditiveLawExample
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector

namespace Formalism.FG

universe u v w

theorem addLawExample : AddLawExample := additive_law_example
theorem notLawExample : NotLawExample := not_a_law_example
theorem funEqHomV : FunEqHomV.{u, v, w} := functional_equation_hom_vector

end Formalism.FG
