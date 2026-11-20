import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedLatticeIsLattice
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_lattice_isLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    Submodule.IsLattice E (L0 σ J X Y L) := by
  first | exact @GlobalTheory.EisRestrict.restrictedLattice_isLattice | exact GlobalTheory.EisRestrict.restrictedLattice_isLattice | (intros; apply GlobalTheory.EisRestrict.restrictedLattice_isLattice <;> assumption)
