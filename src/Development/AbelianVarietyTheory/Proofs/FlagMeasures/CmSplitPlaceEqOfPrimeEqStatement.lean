import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmSplitPlaceEqOfPrimeEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmSplitPlace_eq_of_prime_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L), s.w = s'.w → s = s' := by
  first | exact @GlobalTheory.SplitUniqSer.splitPlace_unique | exact GlobalTheory.SplitUniqSer.splitPlace_unique | (intros; apply GlobalTheory.SplitUniqSer.splitPlace_unique <;> assumption)
