import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Base
namespace UpperTheory.V.Z.Bc
structure HypothesesZ' : Prop where
  af : _root_.UpperTheory.V.Af.Hypotheses'
  eg : PropEG
  up : UpSol
end UpperTheory.V.Z.Bc
end
end
