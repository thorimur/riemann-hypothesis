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

namespace GroundTheory.ProfCoh

def coprimePart (p : ℕ) (Q : Type*) [Group Q] : Subgroup Q :=
  Subgroup.closure {x : Q | (orderOf x).Coprime p}

def primaryPart (p : ℕ) (Q : Type*) [Group Q] : Subgroup Q :=
  Subgroup.closure {x : Q | ∃ n : ℕ, orderOf x = p ^ n}

variable {G : Type*} [Group G]

def coprimeQuotientPreimage (N : Subgroup G) [N.Normal] (p : ℕ) : Subgroup G :=
  (coprimePart p (G ⧸ N)).comap (QuotientGroup.mk' N)

def primaryQuotientPreimage (N : Subgroup G) [N.Normal] (p : ℕ) : Subgroup G :=
  (primaryPart p (G ⧸ N)).comap (QuotientGroup.mk' N)

def coprimeRelPreimage (N₀ N₁ : Subgroup G) [N₁.Normal] (p : ℕ) : Subgroup G :=
  (coprimeQuotientPreimage (N₁.subgroupOf N₀) p).map N₀.subtype

end GroundTheory.ProfCoh
