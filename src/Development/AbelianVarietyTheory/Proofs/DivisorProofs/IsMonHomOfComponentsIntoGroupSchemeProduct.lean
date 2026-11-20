import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.Serre

theorem isMonHom_of_components : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ := by
  intro T A' B' C _ _ _ r pr' hpr huniv Φ hΦ
  have hcomp : ∀ u, IsMonHom (pr' u) := hpr
  have hΦu : ∀ u, IsMonHom (Φ ≫ pr' u) := hΦ
  refine ⟨?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := huniv (𝟙_ (Over T)) (fun u => η[C] ≫ Φ ≫ pr' u)
    have h1 : η[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (η[B'] : 𝟙_ (Over T) ⟶ B') = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [IsMonHom.one_hom, IsMonHom.one_hom (Φ ≫ pr' u)])
    rw [h1, h2]
  · obtain ⟨x, -, hx⟩ := huniv (C ⊗ C) (fun u => μ[C] ≫ Φ ≫ pr' u)
    have h1 : μ[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (Φ ⊗ₘ Φ) ≫ μ[B'] = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [Category.assoc, IsMonHom.mul_hom (Φ ≫ pr' u), IsMonHom.mul_hom (pr' u),
        ← Category.assoc, tensorHom_comp_tensorHom])
    rw [h1, h2]

end GlobalTheory.Serre
