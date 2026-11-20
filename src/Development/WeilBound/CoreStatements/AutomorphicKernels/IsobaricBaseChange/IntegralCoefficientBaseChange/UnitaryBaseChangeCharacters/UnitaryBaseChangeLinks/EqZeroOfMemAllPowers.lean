import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemAllPowers
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.eq_zero_of_mem_all_powers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P), (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 := by
  first | exact @GlobalTheory.NormEq.sep | (intros; apply GlobalTheory.NormEq.sep <;> assumption)
