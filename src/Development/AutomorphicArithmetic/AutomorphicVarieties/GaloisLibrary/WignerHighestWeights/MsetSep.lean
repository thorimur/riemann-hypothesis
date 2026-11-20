import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultisetSeparation
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.msetSep :
    ∀ m m' : Multiset ℂ, (∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) → m = m' :=
  _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep
