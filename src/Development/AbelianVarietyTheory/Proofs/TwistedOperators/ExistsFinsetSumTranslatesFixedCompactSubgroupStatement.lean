import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroup
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finsetSum_translates_fixed_compactSubgroup : ∀ {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) (K : Subgroup G), IsCompact (K : Set G) → ∀ x : X, IsOpen {g | ρ g x = x} → ∃ s : Finset G, (∀ g ∈ s, g ∈ K) ∧ s.Nonempty ∧ ∀ k ∈ K, ρ k (∑ g ∈ s, ρ g x) = ∑ g ∈ s, ρ g x := by
  first | exact @GlobalTheory.exists_finset_sum_translate_fixed | exact GlobalTheory.exists_finset_sum_translate_fixed | (intros; apply GlobalTheory.exists_finset_sum_translate_fixed <;> assumption)
