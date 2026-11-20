import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableLatticeCompactGroup
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_lattice_compact_group : ∀ {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp LL O : Type} [Field Qp] [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O), Nonempty (Lattice (O := O) A.ρ) := by
  first | exact @GlobalTheory.StableLat.exists_lattice | exact GlobalTheory.StableLat.exists_lattice | (intros; apply GlobalTheory.StableLat.exists_lattice <;> assumption)
