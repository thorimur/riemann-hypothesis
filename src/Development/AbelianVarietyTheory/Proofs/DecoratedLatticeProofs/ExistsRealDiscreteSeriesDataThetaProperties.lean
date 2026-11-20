import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARParts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NoThetaLiftDiscreteSeriesSmallerTowerMemberStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaceTheta

theorem exists_record_theta_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, ChosenSeries X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X := by
  intro hD hH
  obtain ⟨X, hX, d1, q5, a1, a2, a3, a5⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta hD hH
  exact ⟨X, hX, a1, a2, a3,
    GlobalTheory.T.no_thetaLift_discreteSeries_smaller_tower_member X (GlobalTheory.FockDeg.degrees_and_adjoints X) (GlobalTheory.FockAlg.fock_structure X) d1 q5, a5⟩

end GlobalTheory.RealPlaceTheta
