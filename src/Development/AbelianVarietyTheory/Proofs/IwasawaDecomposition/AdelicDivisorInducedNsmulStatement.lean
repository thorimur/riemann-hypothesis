import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNsmul
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_divisor_induced_nsmul : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (m : ℕ+) (R : ℝ) (w : Sym D.host.E →₀ ℤ) (L : GlobalTheory.HermLB M.p), (∀ a ∈ w.support, a.2.1 = some R) → (adlOf (Φ.C k) (metsOf x Φ k) w).Induced M L m 0 → ∀ n : ℕ, (adlOf (Φ.C k) (metsOf x Φ k) (n • w)).Induced M (L.pow n) m 0 := by
  first | exact @GlobalTheory.CombPow.induced_nsmul | exact GlobalTheory.CombPow.induced_nsmul | (intros; apply GlobalTheory.CombPow.induced_nsmul <;> assumption)
