import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod

noncomputable section

namespace PositivityTheory.ThKF

open GlobalTheory.ThK

theorem iLeft (hT : ThetaBasic) : ILeft := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ hΦ g =>
  I_left unimodularity_holds hT hp hΦ g

theorem kCoinv (h : KP) : KCoinv := PositivityTheory.KCo.kCoinv_of_dict h.base.bernsteinUnitaryProductIrreducible PositivityTheory.KCo.dictionary_statement

end PositivityTheory.ThKF

end
