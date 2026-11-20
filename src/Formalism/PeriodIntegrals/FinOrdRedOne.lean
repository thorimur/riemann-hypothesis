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

namespace PI.FinOrdRedOne

open NumberField IsDedekindDomain Ideal

abbrev OP (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Type :=
  P.adicCompletionIntegers E

def red {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (OP E P)) :
    Matrix (Fin N) (Fin N) (IsLocalRing.ResidueField (OP E P)) :=
  M.map (IsLocalRing.residue (OP E P))

def Unram (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})], Q.ramificationIdx ℤ = 1

end PI.FinOrdRedOne

namespace PI

open NumberField IsDedekindDomain Ideal PI.FinOrdRedOne

def FinOrdRedOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → 3 ≤ p → Unram E p →
  ∀ (P : HeightOneSpectrum (𝓞 E)), (p : 𝓞 E) ∈ P.asIdeal →
  ∀ (N : ℕ) (β : GL (Fin N) (OP E P)), IsOfFinOrder β →
    red (β : Matrix (Fin N) (Fin N) (OP E P)) = 1 → β = 1

end PI
