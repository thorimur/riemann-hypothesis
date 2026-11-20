import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.DzNarrow
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.DepthZeroInertiaBigOfNarrowBig
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity

namespace UpperTheory.Lit.Dz

theorem big (hL : GlobalTheory.Published.LocalLanglandsGL) : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig :=
  depthZeroInertiaBig_of_narrowBig (narrowBig PositivityTheory.Stage1.PM.globalArtinReciprocity hL)
    PositivityTheory.Stage1.PM.globalArtinReciprocity hL

end UpperTheory.Lit.Dz
