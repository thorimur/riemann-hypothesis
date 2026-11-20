import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFactorsOfMonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKlingenDeligneRibetOfBoth

namespace PositivityTheory.Prw

theorem greenSeriesSt_of (h : GlobalTheory.Published.GreenCuspidal) : GlobalTheory.Published.GreenSeriesSt :=
  GlobalTheory.GreenSeries.green_series h

theorem siegelKlingenDeligneRibet_of (h₁ : GlobalTheory.Published.SiegelKlingen) (h₂ : GlobalTheory.Published.DeligneRibet) :
    GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  GlobalTheory.siegelKlingenDeligneRibet_of_both h₁ h₂

end PositivityTheory.Prw
