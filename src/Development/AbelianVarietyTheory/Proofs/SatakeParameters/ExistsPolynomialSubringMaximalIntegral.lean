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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
open GlobalTheory.EtC

namespace GlobalTheory

theorem exists_polySubring_maximal_integral (k K : Type) [Field k] [Field K] (φ : k →+* K) :
    ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧
      ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  letI : Algebra k K := φ.toAlgebra
  haveI : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).2 φ.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  set A : Subalgebra k K := Algebra.adjoin k (Set.range ((↑) : s → K)) with hA
  let ε : A →ₐ[k] k := (MvPolynomial.aeval (fun _ : s => (0 : k))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hε : ∀ c : k, ε (algebraMap k A c) = c := fun c => ε.commutes c
  let D : Subring K := A.toSubring
  let εD : D →+* k := (ε : A →+* k)
  have hεs : Function.Surjective εD := fun c => ⟨algebraMap k A c, hε c⟩
  refine ⟨D, RingHom.ker εD, ?_, RingHom.ker_isMaximal_of_surjective εD hεs, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact A.algebraMap_mem c
  · intro r
    refine ⟨εD r, A.algebraMap_mem _, ?_⟩
    rw [RingHom.mem_ker, map_sub]
    have : εD ⟨φ (εD r), A.algebraMap_mem _⟩ = εD r := hε (εD r)
    rw [this, sub_self]
  · intro x
    haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic
    haveI : Algebra.IsAlgebraic D K := ‹Algebra.IsAlgebraic A K›
    obtain ⟨y, hy, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := D) x).exists_integral_multiple
    exact ⟨y, hy, by rwa [Algebra.smul_def] at hint⟩

end GlobalTheory
