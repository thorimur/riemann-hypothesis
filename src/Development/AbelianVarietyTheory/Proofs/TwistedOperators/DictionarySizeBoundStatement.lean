import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionarySizeBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_size_bound : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun ch => GlobalTheory.SumSize.DictAt ch := by
  first | exact @GlobalTheory.DictFree.dictAt_big | exact GlobalTheory.DictFree.dictAt_big | (intros; apply GlobalTheory.DictFree.dictAt_big <;> assumption)
