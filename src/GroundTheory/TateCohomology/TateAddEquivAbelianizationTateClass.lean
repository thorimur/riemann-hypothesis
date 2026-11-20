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
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupHomology TensorProduct Finsupp

universe u

section General

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) [A.IsTrivial]

noncomputable def h1Class (g : G) (a : A) : H1 A :=
  H1π A ((cycles₁IsoOfIsTrivial A).inv (single g a))

noncomputable def h1AddEquivAbelianization (e : A ≃+ ℤ) :
    H1 A ≃+ Additive (Abelianization G) :=
  (H1AddEquivOfIsTrivial A).trans <|
    ((TensorProduct.congr (LinearEquiv.refl ℤ (Additive (Abelianization G)))
      e.toIntLinearEquiv).trans (TensorProduct.rid ℤ (Additive (Abelianization G)))).toAddEquiv

end General

section Tate

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

noncomputable def tateNegTwoIsoH1 : tateCohomology A (-2) ≅ H1 A :=
  (TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A

variable [A.IsTrivial]

noncomputable def tateClass (g : G) (a : A) : tateCohomology A (-2) :=
  (tateNegTwoIsoH1 A).inv (h1Class A g a)

noncomputable def tateAddEquivAbelianization (e : A ≃+ ℤ) :
    tateCohomology A (-2) ≃+ Additive (Abelianization G) :=
  (tateNegTwoIsoH1 A).toLinearEquiv.toAddEquiv.trans (h1AddEquivAbelianization A e)

end Tate

section Int

variable (G : Type) [Group G]

noncomputable def h1IntAddEquiv : H1 (Rep.trivial ℤ G ℤ) ≃+ Additive (Abelianization G) :=
  h1AddEquivAbelianization (Rep.trivial ℤ G ℤ) (AddEquiv.refl ℤ)

noncomputable def h1IntIso :
    H1 (Rep.trivial ℤ G ℤ) ≅ ModuleCat.of ℤ (Additive (Abelianization G)) :=
  (h1IntAddEquiv G).toIntLinearEquiv.toModuleIso

variable [Fintype G]

noncomputable def tateIntAddEquiv :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≃+ Additive (Abelianization G) :=
  tateAddEquivAbelianization (Rep.trivial ℤ G ℤ) (AddEquiv.refl ℤ)

noncomputable def tateIntIso :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≅ ModuleCat.of ℤ (Additive (Abelianization G)) :=
  (tateIntAddEquiv G).toIntLinearEquiv.toModuleIso

end Int

section ULiftInt

variable (G : Type u) [Group G]

noncomputable def h1ULiftIntAddEquiv :
    H1 (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) ≃+ Additive (Abelianization G) :=
  h1AddEquivAbelianization (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) AddEquiv.ulift

variable [Fintype G]

noncomputable def tateULiftIntAddEquiv :
    tateCohomology (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) (-2) ≃+
      Additive (Abelianization G) :=
  tateAddEquivAbelianization (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) AddEquiv.ulift

end ULiftInt

end GroundTheory.GroupCoh
