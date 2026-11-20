import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLevi
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_smul_of_central_parabolicLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  first | exact @GlobalTheory.CentralLevi.exists_unit_smul_of_central | exact GlobalTheory.CentralLevi.exists_unit_smul_of_central | (intros; apply GlobalTheory.CentralLevi.exists_unit_smul_of_central <;> assumption)
