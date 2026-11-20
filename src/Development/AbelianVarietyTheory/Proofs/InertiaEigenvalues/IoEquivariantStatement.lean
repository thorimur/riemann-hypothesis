import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.io_equivariant_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  first | exact @GlobalTheory.Cyc.Decomp.io_equivariant | exact GlobalTheory.Cyc.Decomp.io_equivariant | (intros; apply GlobalTheory.Cyc.Decomp.io_equivariant <;> assumption)
