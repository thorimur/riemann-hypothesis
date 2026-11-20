import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteReproducingFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_K_finite_reproducing_function : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG ε) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∃ e : Formalism.REAL.KG ε → ℂ, KFinFun ε e ∧ ∀ h ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, ∫ k, e k * h k ∂(Formalism.REAL.muK ε) = h 1 := by
  first | exact @GlobalTheory.ReproKFin.reproduce_one | exact GlobalTheory.ReproKFin.reproduce_one | (intros; apply GlobalTheory.ReproKFin.reproduce_one <;> assumption)
