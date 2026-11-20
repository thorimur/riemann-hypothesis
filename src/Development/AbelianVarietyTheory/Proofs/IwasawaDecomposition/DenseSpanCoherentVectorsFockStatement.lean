import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseSpanCoherentVectorsFock
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_span_coherent_vectors_fock : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (e : (Ix P Q → ℂ) → F.H), (∀ x, HasCoeff F (e x) (expPS (gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x))) → Dense (Submodule.span ℂ (Set.range e) : Set F.H) := by
  first | exact @GlobalTheory.dense_span_coherent | exact GlobalTheory.dense_span_coherent | (intros; apply GlobalTheory.dense_span_coherent <;> assumption)
