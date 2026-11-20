import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoprimeIdeleApproximation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_coprime_idele_approximation : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (k n : ℕ), 0 < n → k ∣ n → ∀ m : K, m ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) →
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ |((Algebra.norm ℚ m : ℚ) : ℝ)| = b / modF t := by
  first | exact @GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF | exact GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF | (intros; apply GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF <;> assumption)
