import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFiniteAdelesDenseRational
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_finite_adeles_dense_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite <;> assumption)
