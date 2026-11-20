import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdCardAdicCompletionIntegersQuotDvdPowFinrank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank | exact GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank | (intros; apply GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank <;> assumption)
