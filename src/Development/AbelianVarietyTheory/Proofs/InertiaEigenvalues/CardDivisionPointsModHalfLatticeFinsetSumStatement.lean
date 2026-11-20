import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsModHalfLatticeFinsetSum
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_divisionPointsModHalfLattice_finset_sum : ∀ {D : D7} {S T : HSp D} (Λ : AddSubgroup (WO S T)), (∀ c : AE D, c * c = c → ∀ u ∈ Λ, c • u ∈ Λ) → ∀ {ι : Type} (s : Finset ι) (cs : ι → AE D), (∀ i ∈ s, cs i * cs i = cs i) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) → ∀ N : ℕ, Nat.card (GlobalTheory.DivPtFourier.DQ Λ (∑ i ∈ s, cs i) N) = ∏ i ∈ s, Nat.card (GlobalTheory.DivPtFourier.DQ Λ (cs i) N) := by
  first | exact @GlobalTheory.DivPtFourier.card_DQ_sum | exact GlobalTheory.DivPtFourier.card_DQ_sum | (intros; apply GlobalTheory.DivPtFourier.card_DQ_sum <;> assumption)
