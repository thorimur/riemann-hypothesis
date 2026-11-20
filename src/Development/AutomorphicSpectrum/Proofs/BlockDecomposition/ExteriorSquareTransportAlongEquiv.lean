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
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem wedge_transport {R : Type} [CommRing R] {V V' W W' : Type} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V'] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] (u : V ≃ₗ[R] V') (v : W ≃ₗ[R] W') (c : V →ₗ[R] V →ₗ[R] W) (c' : V' →ₗ[R] V' →ₗ[R] W') (h : ∀ a b, v (c a b) = c' (u a) (u b)) (e : ⋀[R]^2 V' ≃ₗ[R] W') (he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = c' a b) : ∃ e' : ⋀[R]^2 V ≃ₗ[R] W, ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = c a b := by
  have h₁ : (u : V →ₗ[R] V') ∘ₗ (u.symm : V' →ₗ[R] V) = LinearMap.id :=
    LinearMap.ext fun x => by simp
  have h₂ : (u.symm : V' →ₗ[R] V) ∘ₗ (u : V →ₗ[R] V') = LinearMap.id :=
    LinearMap.ext fun x => by simp
  let A : ⋀[R]^2 V ≃ₗ[R] ⋀[R]^2 V' :=
    LinearEquiv.ofLinear (exteriorPower.map 2 (u : V →ₗ[R] V'))
      (exteriorPower.map 2 (u.symm : V' →ₗ[R] V))
      (by rw [← exteriorPower.map_comp, h₁, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, h₂, exteriorPower.map_id])
  refine ⟨A.trans (e.trans v.symm), fun a b => ?_⟩
  have hu : (⇑(u : V →ₗ[R] V') ∘ ![a, b]) = ![u a, u b] := by
    funext i
    fin_cases i <;> rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply,
    exteriorPower.map_apply_ιMulti, hu, he, ← h, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.HopfC
