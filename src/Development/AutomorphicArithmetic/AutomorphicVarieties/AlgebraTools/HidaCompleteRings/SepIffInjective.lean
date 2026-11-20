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

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

variable {O R K : Type*} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K]

def Sep (Y : Set (R →ₐ[O] K)) : Prop := ∀ f : R, (∀ y ∈ Y, y f = 0) → f = 0

theorem Sep.mono {Y Y' : Set (R →ₐ[O] K)} (h : Sep Y) (hle : Y ⊆ Y') : Sep Y' :=
  fun f hf => h f fun y hy => hf y (hle hy)

theorem Sep.ext {Y : Set (R →ₐ[O] K)} (h : Sep Y) {a b : R} (hab : ∀ y ∈ Y, y a = y b) : a = b :=
  sub_eq_zero.1 (h _ fun y hy => by rw [map_sub, hab y hy, sub_self])

def kerPt [IsDomain K] (y : R →ₐ[O] K) : PrimeSpectrum R := ⟨RingHom.ker y, RingHom.ker_isPrime y⟩

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
