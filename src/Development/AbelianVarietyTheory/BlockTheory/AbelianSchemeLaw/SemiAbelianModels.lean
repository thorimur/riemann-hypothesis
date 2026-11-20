import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.IsTorus
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels

def IsExtensionByTorus {k : Type} [Field k] {T G B : Over (Spec (CommRingCat.of k))}
    [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsTorus T ∧ IsAbelianScheme B ∧ IsMonHom i ∧ IsMonHom q ∧
    Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
    IsPullback i (toUnit T) q (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B)

noncomputable abbrev fibreAlong {V F : Type} [CommRing V] [CommRing F] (f : V →+* F)
    (G : Over (Spec (CommRingCat.of V))) : Over (Spec (CommRingCat.of F)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj G

def TorusAffineSplitsFinite : Prop :=
  ∀ (k : Type) [Field k] (T : Over (Spec (CommRingCat.of k))) [GrpObj T], IsTorus T →
    IsAffine T.left ∧
      ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
        (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
        (e : fieldBaseChange k L T ≅ splitTorus (Spec (CommRingCat.of L)) X), IsMonHom e.hom

def ResidueExtensionLifts : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (k' : Type) [Field k'] [Algebra (IsLocalRing.ResidueField V) k']
    [Module.Finite (IsLocalRing.ResidueField V) k'],
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V'),
      Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ IsLocalHom (algebraMap V V') ∧
        ∃ e : IsLocalRing.ResidueField V' ≃+* k', ∀ x : V,
          e (IsLocalRing.residue V' (algebraMap V V' x)) =
            algebraMap (IsLocalRing.ResidueField V) k' (IsLocalRing.residue V x)

def ExtensionQuotientAffine : Prop :=
  ∀ (k : Type) [Field k] (T G B : Over (Spec (CommRingCat.of k)))
    [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B),
    IsExtensionByTorus i q → IsAffineHom q.left

def ModelSemiAbelian : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G],
    IsCommMonObj G → Smooth G.hom → IsSeparated G.hom → QuasiCompact G.hom →
    IsAbelianScheme (fibreAlong (algebraMap V K) G) →
    (∃ (T B : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField V))))
      (_ : GrpObj T) (_ : GrpObj B)
      (i : T ⟶ fibreAlong (IsLocalRing.residue V) G) (q : fibreAlong (IsLocalRing.residue V) G ⟶ B),
      IsExtensionByTorus i q) →
    IsSemiAbelian G

def SeamNodes : Prop :=
  TorusAffineSplitsFinite ∧ ResidueExtensionLifts ∧ ExtensionQuotientAffine ∧ ModelSemiAbelian

end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels
