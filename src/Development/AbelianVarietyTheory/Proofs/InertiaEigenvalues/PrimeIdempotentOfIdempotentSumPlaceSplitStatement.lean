import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)), IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧ infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  first | exact @GlobalTheory.IdemSumBranch.branch | exact GlobalTheory.IdemSumBranch.branch | (intros; apply GlobalTheory.IdemSumBranch.branch <;> assumption)
