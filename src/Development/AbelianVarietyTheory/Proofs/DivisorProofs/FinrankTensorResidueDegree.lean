import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.ResidueTensorRank

theorem finrank_pushout_inl {K A B P : CommRingCat.{0}} (hK : IsField K) (hA : IsField A) (a : K ⟶ A) (b : K ⟶ B)
    (i : A ⟶ P) (j : B ⟶ P) (h : IsPushout a b i j) :
    @Module.finrank A P _ _ i.hom.toModule = @Module.finrank K B _ _ b.hom.toModule := by
  letI := hK.toField
  letI := hA.toField
  algebraize [a.hom, b.hom, i.hom, j.hom, (a ≫ i).hom]
  haveI : IsScalarTower K A P := .of_algebraMap_eq' rfl
  haveI : IsScalarTower K B P := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have hp : Algebra.IsPushout K A B P := CommRingCat.isPushout_iff_isPushout.mp h
  exact hp.out.finrank_eq

theorem finrank_tensorInl : ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (T : Scheme.Pullback.Triplet f g), @Module.finrank (X.residueField T.x) T.tensor _ _ T.tensorInl.hom.toModule = g.residueDegree T.y := by
  intro X Y S f g T
  obtain ⟨x, y, s, hx, hy⟩ := T
  subst hy
  have := finrank_pushout_inl (Field.toIsField _) (Field.toIsField _) _ _ _ _ (IsPushout.of_hasPushout ((S.residueFieldCongr hx).inv ≫ f.residueFieldMap x) ((S.residueFieldCongr (rfl : g y = g y)).inv ≫ g.residueFieldMap y))
  refine this.trans ?_
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp]
  rfl

end GlobalTheory.ResidueTensorRank
