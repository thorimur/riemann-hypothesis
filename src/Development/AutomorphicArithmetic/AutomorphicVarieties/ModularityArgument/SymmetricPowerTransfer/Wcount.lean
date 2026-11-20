import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.QuadraticAlgebra.Defs
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

namespace UpperTheory.V.Z.Sym

open MulAction

def gcount (H : Type) {Y : Type} [Group H] [MulAction H Y] (k : Y → ℂ) : ℂ :=
  ∑ᶠ o : orbitRel.Quotient H Y, k o.out / (Nat.card (stabilizer H o.out) : ℂ)

def wcount {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (k : Y → ℂ) : ℂ :=
  ∑ᶠ o : orbitRel.Quotient T Y, ((stabilizer T o.out).relIndex C : ℂ) * k o.out

def orb {T G : Type} [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G) : ℂ :=
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  wcount C fun y : G ⧸ U => f (y.out⁻¹ * δ * θ y.out)

abbrev Etau (R : Type) [CommRing R] (τ : R) : Type := QuadraticAlgebra R (-1) τ

abbrev Lsq (R : Type) [CommRing R] (Δ : R) : Type := QuadraticAlgebra R Δ 0

example : gcount PUnit (fun _ : PUnit => (1 : ℂ)) = gcount PUnit (fun _ : PUnit => (1 : ℂ)) := rfl

end UpperTheory.V.Z.Sym
