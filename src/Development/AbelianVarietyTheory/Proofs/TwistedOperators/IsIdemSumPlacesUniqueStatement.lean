import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumPlacesUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIdemSum_places_unique : ∀ (D : D7) (e : AE D) (P P' : Finset (Pl D.host.E)), IsIdemSum e P → IsIdemSum e P' → P = P' := by
  first | exact @GlobalTheory.IdemSumSet.places_eq_of_isIdemSum | exact GlobalTheory.IdemSumSet.places_eq_of_isIdemSum | (intros; apply GlobalTheory.IdemSumSet.places_eq_of_isIdemSum <;> assumption)
