import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KArith
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

noncomputable section

open CategoryTheory NumberField IsDedekindDomain UpperTheory.V.KL UpperTheory.V.Published
open scoped TensorProduct

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

namespace UpperTheory.V.K

end UpperTheory.V.K

namespace UpperTheory.V

structure Published.KPublished : Prop where
  plusExists : KPlusExists
  acyclicHomology : KAcyclicHomology
  milnor : KMilnor
  hurewicz : KHurewicz
  stability : KStability
  finGen : KFinGen
  borelRank : KBorelRank
  dwyerFriedlander : KDwyerFriedlander

end UpperTheory.V

end
