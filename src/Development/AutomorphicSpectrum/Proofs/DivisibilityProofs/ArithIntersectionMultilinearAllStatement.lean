import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAll
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_intersection_multilinear_all : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin d → J → ℤ), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (fun k => combLine ℓ (n k)) = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine_expansion | exact GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine_expansion | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine_expansion <;> assumption)
