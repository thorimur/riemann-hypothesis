import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingAdelicMatrixBounded
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_preserving_adelic_matrix_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d), W.L.IsLattice E → ∃ K : Set (AE F E), IsCompact K ∧ ∀ A : Matrix (Fin d) (Fin d) (AE F E), At (fun a : AF F => a.2) (A - 1) → (∀ v : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → ∀ i j, A i j ∈ K := by
  first | exact @GlobalTheory.EntriesCompact.entries_mem_compact | exact GlobalTheory.EntriesCompact.entries_mem_compact | (intros; apply GlobalTheory.EntriesCompact.entries_mem_compact <;> assumption)
