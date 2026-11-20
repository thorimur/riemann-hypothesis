import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesMoveRealPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientPoincareSeries_move_real_point : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v₀ : ∀ τ, M.H τ) (g₀ : GA D V), g₀ ∈ GinfC V → ∀ c g : GA D V, poin θ M K v₀ (g₀⁻¹ * c) v₀ (g * g₀) = poin θ M K (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) c (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) g := by
  first | exact @GlobalTheory.PoinConj.poin_conj | exact GlobalTheory.PoinConj.poin_conj | (intros; apply GlobalTheory.PoinConj.poin_conj <;> assumption)
