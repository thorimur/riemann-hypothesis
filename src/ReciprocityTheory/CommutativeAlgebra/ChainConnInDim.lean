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

namespace ReciprocityTheory.CA

open PrimeSpectrum

variable (R : Type*) [CommRing R]

def ConnInDim (k : WithBot ℕ∞) : Prop :=
  ∀ I : Ideal R, ringKrullDim (R ⧸ I) < k → IsConnected ((zeroLocus (I : Set R))ᶜ : Set (PrimeSpectrum R))

def Linked (k : WithBot ℕ∞) (p q : Ideal R) : Prop := k ≤ ringKrullDim (R ⧸ (p ⊔ q))

def ChainConnInDim (k : WithBot ℕ∞) : Prop :=
  (minimalPrimes R).Nonempty ∧
  ∀ p ∈ minimalPrimes R, ∀ q ∈ minimalPrimes R,
    Relation.ReflTransGen (fun a b : Ideal R => a ∈ minimalPrimes R ∧ b ∈ minimalPrimes R ∧ Linked R k a b) p q
    ∧ k ≤ ringKrullDim (R ⧸ p)

def puncturedSpec [IsLocalRing R] : Set (PrimeSpectrum R) := {IsLocalRing.closedPoint R}ᶜ

noncomputable def sdim : WithBot ℕ∞ := ⨅ p ∈ minimalPrimes R, ringKrullDim (R ⧸ p)

def AraLE {R : Type*} [CommRing R] (a : Ideal R) (r : ℕ) : Prop :=
  ∃ s : Finset R, s.card ≤ r ∧ (Ideal.span (s : Set R)).radical = a.radical

def DepthGE [IsLocalRing R] (n : ℕ) : Prop :=
  ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧ RingTheory.Sequence.IsRegular R rs

def IsCM [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ ∃ n : ℕ, ringKrullDim R = n ∧ DepthGE R n

end ReciprocityTheory.CA
