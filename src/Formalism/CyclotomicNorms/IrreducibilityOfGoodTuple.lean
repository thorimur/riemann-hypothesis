import Formalism.CyclotomicNorms.NonsquarefreeBounds.Newton
import Formalism.CyclotomicNorms.NonsquarefreeBounds.Central
import Formalism.CyclotomicNorms.NonsquarefreeBounds.Jordan
import Formalism.CyclotomicNorms.NonsquarefreeBounds.RestrictionOfBlocksAndJordan
import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction

namespace Formalism.CyclotomicNorms

theorem evaluation : Evaluation := evaluation_bound
theorem centralScalar : CentralScalar := central_scalar_holds

theorem restriction : Restriction := restriction_of_blocks_and_jordan blocks_form_cycle jordan_transitivity

theorem irreducibility_of_good_tuple : IrreducibilityCriterion := irreducibility_of_restriction restriction

end Formalism.CyclotomicNorms
