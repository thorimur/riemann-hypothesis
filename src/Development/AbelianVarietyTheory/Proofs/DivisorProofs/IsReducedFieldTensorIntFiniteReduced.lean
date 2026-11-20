import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FinRedTensor

theorem formallyUnramified_int_of_finite_field (K : Type) [Field K] [Finite K] :
    Algebra.FormallyUnramified ℤ K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : NeZero p := ⟨CharP.char_ne_zero_of_finite K p⟩
  haveI : Fact p.Prime := CharP.char_is_prime_of_pos K p
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Module.Finite (ZMod p) K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (ZMod p) K := inferInstance
  haveI : Algebra.FormallyUnramified (ZMod p) K := Algebra.FormallyUnramified.of_isSeparable _ _
  haveI : Algebra.FormallyUnramified ℤ (ZMod p) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (ZMod p)) (ZMod.intCast_surjective)
  exact Algebra.FormallyUnramified.comp ℤ (ZMod p) K

theorem formallyUnramified_int_of_finite_isReduced (A : Type) [CommRing A] [Finite A]
    [IsReduced A] : Algebra.FormallyUnramified ℤ A := by
  haveI : IsArtinianRing A := inferInstance
  have h : Algebra.FormallyUnramified ℤ (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    haveI : Finite (A ⧸ I.asIdeal) :=
      Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
    exact formallyUnramified_int_of_finite_field _
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars ℤ).symm

theorem isReduced_field_tensor_finite :
    ∀ (A : Type) [CommRing A] [Finite A] [IsReduced A] (k : Type) [Field k],
      IsReduced (k ⊗[ℤ] A) := by
  intro A _ _ _ k _
  haveI := formallyUnramified_int_of_finite_isReduced A
  haveI : Algebra.FormallyUnramified k (k ⊗[ℤ] A) := Algebra.FormallyUnramified.base_change k
  haveI : Module.Finite ℤ A := Module.Finite.of_finite
  haveI : Algebra.EssFiniteType k (k ⊗[ℤ] A) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field k _

end GlobalTheory.FinRedTensor
