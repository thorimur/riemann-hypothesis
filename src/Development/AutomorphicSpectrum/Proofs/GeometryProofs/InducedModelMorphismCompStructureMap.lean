import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem embedding_const_preconnected {F : Type} [Field F] [NumberField F] {m : ℕ} {B : Set (Fin m → ℂ)} (hpre : IsPreconnected B)
    (κ : (Fin m → ℂ) → (F →+* ℂ))
    (hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) B) {b b' : Fin m → ℂ} (hb : b ∈ B) (hb' : b' ∈ B) :
    κ b = κ b' := by
  have key : ∀ x : 𝓞 F, κ b (x : F) = κ b' (x : F) := by
    intro x
    have hT : IsDiscrete (Set.range fun s : F →+* ℂ => s (x : F)) :=
      (Set.finite_range _).isDiscrete
    have hmaps : Set.MapsTo (fun c => κ c (x : F)) B (Set.range fun s : F →+* ℂ => s (x : F)) :=
      fun c _ => ⟨κ c, rfl⟩
    exact hpre.constant_of_mapsTo hT (hd x).continuousOn hmaps hb hb'
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
  ext x
  exact key x

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
