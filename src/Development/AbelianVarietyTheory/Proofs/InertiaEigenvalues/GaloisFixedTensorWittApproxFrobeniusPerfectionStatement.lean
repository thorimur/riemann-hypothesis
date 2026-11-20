import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittApproxFrobeniusPerfection
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisFixedTensorWitt_approx_frobeniusPerfection : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ y ∈ fixSub AI LL (Hinf K : Set (GQ l)), ∀ m : ℕ, ∃ (n : ℕ) (y0 : RW LL) (e : W.EE) (r : RW LL), (φRW LL)^[n] y0 = E.tie.ioE e + (l : RW LL) * r ∧ NearPi AI LL s m (y - y0) := by
  first | exact @GlobalTheory.DecomplDense.fixSub_approx_perfection | exact GlobalTheory.DecomplDense.fixSub_approx_perfection | (intros; apply GlobalTheory.DecomplDense.fixSub_approx_perfection <;> assumption)
