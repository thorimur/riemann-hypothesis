import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_integral_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  first | exact @GlobalTheory.CycIntegral.cyc_lattice | exact GlobalTheory.CycIntegral.cyc_lattice | (intros; apply GlobalTheory.CycIntegral.cyc_lattice <;> assumption)
