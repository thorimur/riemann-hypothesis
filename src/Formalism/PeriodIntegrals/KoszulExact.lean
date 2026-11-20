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
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Regular.RegularSequence
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

noncomputable section

namespace PI.KoszulExact

def form {R : Type*} [CommRing R] {D : ℕ} (s : Fin D → R) : Module.Dual R (Fin D → R) :=
  ∑ i, s i • (LinearMap.proj i : (Fin D → R) →ₗ[R] R)

def dK {R : Type*} [CommRing R] {D : ℕ} (s : Fin D → R) :
    ExteriorAlgebra R (Fin D → R) →ₗ[R] ExteriorAlgebra R (Fin D → R) :=
  CliffordAlgebra.contractLeft (form s)

end PI.KoszulExact

namespace PI

def KoszulExact.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
      (∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)), x ∈ ⋀[R]^(j + 1) (Fin D → R) →
          KoszulExact.dK s x = 0 → ∃ y ∈ ⋀[R]^(j + 2) (Fin D → R), KoszulExact.dK s y = x) ∧
      (∀ r : R, (∃ y ∈ ⋀[R]^1 (Fin D → R), KoszulExact.dK s y = algebraMap R _ r) ↔
          r ∈ Ideal.span (Set.range s))

end PI
