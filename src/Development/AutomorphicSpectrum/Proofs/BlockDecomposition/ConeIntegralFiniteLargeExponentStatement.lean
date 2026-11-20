import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralFiniteLargeExponent
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_integral_finite_large_exponent : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) (c : ℝ), 0 < c → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top | exact GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top | (intros; apply GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top <;> assumption)
