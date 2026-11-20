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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.genSpan :
    ∀ {A G : Type} [CommRing A] [Group G] (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G),
    ∃ (m : ℕ) (g : Fin m → G) (b : Fin m → B), x = ∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single (g j) 1) := by
  intro A G _ _ B _ _ x
  have hs : ∀ g : G, MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single g 1)
      = MonoidAlgebra.single g (1 : B) := by
    intro g
    simp
  simp only [hs]
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    exact ⟨1, fun _ => g, fun _ => 1, by simp [MonoidAlgebra.of_apply]⟩
  | add x y hx hy =>
    obtain ⟨m, g, b, rfl⟩ := hx
    obtain ⟨n, h, c, rfl⟩ := hy
    refine ⟨m + n, Fin.append g h, Fin.append b c, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r x hx =>
    obtain ⟨m, g, b, rfl⟩ := hx
    refine ⟨m, g, fun j => r * b j, ?_⟩
    rw [Finset.smul_sum]
    simp [smul_smul]
