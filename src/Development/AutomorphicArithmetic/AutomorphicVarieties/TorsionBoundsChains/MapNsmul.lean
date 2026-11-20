import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
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

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.mapNsmul :
    ∀ (G : Type) [Group G] (A B : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ A) (n j : ℕ),
      (∀ a, g.hom (f.hom a) = n • a) → Subsingleton (groupHomology B j) →
      ∀ z : groupHomology A j, n • z = 0 := by
  intro G _ A B f g n j h hB z
  have hc : groupHomology.chainsMap (MonoidHom.id G) (f ≫ g) =
      n • 𝟙 (groupHomology.inhomogeneousChains A) := by
    ext i : 1
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun c => ?_
    refine Finsupp.ext fun y => ?_
    simp [h]
  have hm : groupHomology.map (MonoidHom.id G) (f ≫ g) j = n • 𝟙 (groupHomology A j) := by
    simp only [groupHomology.map, hc]
    change (HomologicalComplex.homologyFunctor _ _ j).map _ = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have e1 : (groupHomology.map (MonoidHom.id G) (f ≫ g) j).hom z = n • z := by
    rw [hm]
    rfl
  rw [← e1, groupHomology.map_id_comp]
  have e2 : (groupHomology.map (MonoidHom.id G) f j).hom z = 0 :=
    Subsingleton.elim (α := groupHomology B j) _ _
  simp [e2]
