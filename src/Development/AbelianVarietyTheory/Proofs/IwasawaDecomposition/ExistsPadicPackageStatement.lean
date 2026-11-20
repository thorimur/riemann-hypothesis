import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicPackage
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padic_package : ∀ D : D7, ∃ ng : NgPkg, ∀ (N j : ℕ) (Comp : Type) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)), j ≤ N → Nonempty (PadPkg D N j Comp jC ng) := by
  first | exact @GlobalTheory.nonempty_provisionalPadPkg | exact GlobalTheory.nonempty_provisionalPadPkg | (intros; apply GlobalTheory.nonempty_provisionalPadPkg <;> assumption)
