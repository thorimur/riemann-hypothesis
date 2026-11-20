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

noncomputable section

namespace DiscreteGroups.sglob.Stick

open NumberField IsDedekindDomain nonZeroDivisors

universe u

def dsum (p a : ℕ) : ℕ := (Nat.digits p a).sum

def psi (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Algebra (ZMod p) k] {A : Type*} [CommRing A]
    (ζ : A) (hζ : ζ ^ p = 1) : AddChar k A :=
  (AddChar.zmodChar p hζ).compAddMonoidHom (Algebra.trace (ZMod p) k).toAddMonoidHom

structure GSDatum (p f : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (A : Type*) [CommRing A] [IsDedekindDomain A] (Q : HeightOneSpectrum A) where
  card_eq : Fintype.card k = p ^ f
  ι : k →+* A ⧸ Q.asIdeal
  ω : MulChar k A
  mk_ω : ∀ x, Ideal.Quotient.mk Q.asIdeal (ω x) = ι x
  ζ : A
  prim : IsPrimitiveRoot ζ p

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}

def ψ (D : GSDatum p f k A Q) : AddChar k A := psi p k D.ζ D.prim.pow_eq_one

def g (D : GSDatum p f k A Q) (a : ℕ) : A := gaussSum (D.ω ^ a)⁻¹ D.ψ

end GSDatum
end DiscreteGroups.sglob.Stick
