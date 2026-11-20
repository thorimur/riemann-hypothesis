import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondG_sAnd_of_largeBase : ∀ (KP : GroupRetwisting.BaseP) (Q Q' R : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.LargeBaseConditionG KP Q R → GroupRetwisting.SecondG KP Q Q' → GroupRetwisting.SecondG KP Q (sAnd Q' R) := by
  first | exact @GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase | exact GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase | (intros; apply GlobalTheory.Mem.Top.GroupRetwisting.SecondG.sAnd_of_largeBase <;> assumption)
