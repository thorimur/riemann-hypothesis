import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
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

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat

noncomputable def fieldUnits (N : ℕ) [NeZero N] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) : Subgroup (ZMod N)ˣ :=
  E.fixingSubgroup.map (galEquivZMod N K).toMonoidHom

noncomputable def fieldChars (N : ℕ) [NeZero N] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) :
    Subgroup (DirichletCharacter ℂ N) :=
  annihilator ℂ (fieldUnits N E : Set (ZMod N)ˣ)

open Classical in

noncomputable def rootWeight (l m : ℕ) : ℚ :=
  if m ≠ 1 ∧ ∃ s, m = l ^ s then 1 / (Nat.totient m : ℚ) else 0

end KStar.Ram
