import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.exists_section_of_integral_surjective_algClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of K)) [IsIntegralHom g] [Surjective g], ∃ s : Spec (CommRingCat.of K) ⟶ Y, s ≫ g = 𝟙 _ := by
  intro K _ _ Y g _ _
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨y, -⟩ := g.surjective (IsLocalRing.closedPoint K)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := Y)).exists_closed_singleton ⟨y, trivial⟩
  haveI : IsIntegralHom (Y.fromSpecResidueField x ≫ g) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hx
    infer_instance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = Y.fromSpecResidueField x ≫ g :=
    ⟨_, Spec.map_preimage _⟩
  haveI : IsIso φ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, hφ]
    infer_instance
  refine ⟨Spec.map (inv φ) ≫ Y.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  simp
