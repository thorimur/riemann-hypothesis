import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergAverageCompactSymplecticTrivial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergAverage_compactSymplecticTrivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (K : AddSubgroup (WO A T)), IsCompact (K : Set (WO A T)) → (∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1) → ∀ (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∃ g : WO A T → ℂ, Continuous g ∧ (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), g (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * g u) ∧ (∀ u ∈ K, heisO ψ A T u g = g) ∧ ∀ δ : ℝ, (∀ a ∈ K, ∀ w, ‖heisO ψ A T a q w - q w‖ ≤ δ) → ∀ w, ‖g w - q w‖ ≤ δ := by
  first | exact @GlobalTheory.HeisAvgCompact.exists_average | exact GlobalTheory.HeisAvgCompact.exists_average | (intros; apply GlobalTheory.HeisAvgCompact.exists_average <;> assumption)
