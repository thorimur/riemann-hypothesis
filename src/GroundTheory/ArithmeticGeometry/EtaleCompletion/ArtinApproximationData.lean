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
import Mathlib.RingTheory.Radical.NatInt
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open IsLocalRing

noncomputable def jacobianMinor {R : Type*} [CommRing R] {m n : ℕ}
    (g : Fin m → MvPolynomial (Fin n) R) (ι : Fin m → Fin n) : MvPolynomial (Fin n) R :=
  (Matrix.of fun i j ↦ MvPolynomial.pderiv (ι j) (g i)).det

structure IsAdicCompletionMap {A : Type*} [CommRing A] [IsLocalRing A] {C : Type*} [CommRing C]
    (φ : A →+* C) : Prop where
  isAdicComplete : IsAdicComplete ((maximalIdeal A).map φ) C
  bijective : ∀ n : ℕ, Function.Bijective
    (Ideal.quotientMap ((maximalIdeal A ^ n).map φ) φ Ideal.le_comap_map)

end GroundTheory.Arith.Etale
