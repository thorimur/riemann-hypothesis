import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelSubbundleIsVB
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_subbundle_isVB : ∀ (X : Scheme.{0}) (G E : X.Modules) (i : G ⟶ E) (n l : ℕ) (hl : l ≤ n), Mono i → (∀ x : X, ∃ (U : X.Opens) (e : Fin n → Γ(E, U)) (f : Fin l → Γ(G, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame e ∧ GlobalTheory.VB.IsFrame f ∧ ∀ j, i.app U (f j) = e (Fin.castLE hl j)) → GlobalTheory.VB.IsVB (cokernel i) (n - l) := by
  first | exact @GlobalTheory.VB.isVB_cokernel_of_frames | exact GlobalTheory.VB.isVB_cokernel_of_frames | (intros; apply GlobalTheory.VB.isVB_cokernel_of_frames <;> assumption)
