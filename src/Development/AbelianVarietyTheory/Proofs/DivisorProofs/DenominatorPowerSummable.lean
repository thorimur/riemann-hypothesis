import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.AffGlue

end GlobalTheory.AffGlue

namespace GlobalTheory.AffGlue

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in

theorem _root_.GlobalTheory.AffGlue.existsUnique_ringHom_of_affineOpens : ∀ (Z : Scheme.{0}) (R : Type) [CommRing R] (φ : ∀ U : Z.affineOpens, R →+* Γ(Z, U)), (∀ (U V : Z.affineOpens) (h : (U : Z.Opens) ≤ V), (Z.presheaf.map (homOfLE h).op).hom.comp (φ V) = φ U) → ∃! Φ : R →+* Γ(Z, ⊤), ∀ U : Z.affineOpens, (Z.presheaf.map (homOfLE (le_top : (U : Z.Opens) ≤ ⊤)).op).hom.comp Φ = φ U := by
  intro Z R _ φ hφ
  have hcomp : ∀ {A B C : Z.Opens} (f : A ⟶ B) (g : B ⟶ C) (s : Γ(Z, C)),
      (Z.presheaf.map f.op).hom ((Z.presheaf.map g.op).hom s) =
        (Z.presheaf.map (f ≫ g).op).hom s := by
    intro A B C f g s
    rw [op_comp, Functor.map_comp]
    rfl
  have hφ' : ∀ (U V : Z.affineOpens) (f : (U : Z.Opens) ⟶ V) (r : R),
      (Z.presheaf.map f.op).hom (φ V r) = φ U r := by
    intro U V f r
    rw [show f = homOfLE (leOfHom f) from Subsingleton.elim _ _]
    exact RingHom.congr_fun (hφ U V (leOfHom f)) r
  have hcov : ∀ V : Z.Opens,
      V ≤ ⨆ W : {W : Z.affineOpens // (W : Z.Opens) ≤ V}, (W.1 : Z.Opens) := by
    intro V x hx
    obtain ⟨W, hW, hxW, hWle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hxW⟩
  have hglue : ∀ r : R, ∃! s : Γ(Z, ⊤), ∀ W : Z.affineOpens,
      (Z.presheaf.map (homOfLE (le_top : (W : Z.Opens) ≤ ⊤)).op).hom s = φ W r := by
    intro r
    have htop : (⊤ : Z.Opens) ≤ ⨆ W : Z.affineOpens, (W : Z.Opens) := by
      intro x hx
      obtain ⟨W, hW, hxW, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hxW⟩
    refine Z.sheaf.existsUnique_gluing' (fun W : Z.affineOpens => (W : Z.Opens)) ⊤
      (fun W => homOfLE le_top) htop (fun W => φ W r) ?_
    intro i j
    refine Z.sheaf.eq_of_locally_eq'
      (fun k : {W : Z.affineOpens // (W : Z.Opens) ≤ (i : Z.Opens) ⊓ j} => (k.1 : Z.Opens))
      _ (fun k => homOfLE k.2) (hcov _) _ _ fun k => ?_
    change (Z.presheaf.map _).hom ((Z.presheaf.map _).hom (φ i r)) =
      (Z.presheaf.map _).hom ((Z.presheaf.map _).hom (φ j r))
    rw [hcomp, hcomp, hφ', hφ']
  choose s hs hu using hglue
  let Φ : R →+* Γ(Z, ⊤) :=
    { toFun := s
      map_one' := (hu 1 1 fun W => by rw [map_one, map_one]).symm
      map_mul' := fun a b => (hu (a * b) (s a * s b) fun W => by
        rw [map_mul, hs a W, hs b W, map_mul]).symm
      map_zero' := (hu 0 0 fun W => by rw [map_zero, map_zero]).symm
      map_add' := fun a b => (hu (a + b) (s a + s b) fun W => by
        rw [map_add, hs a W, hs b W, map_add]).symm }
  refine ⟨Φ, fun W => RingHom.ext fun r => hs r W,
    fun Ψ hΨ => RingHom.ext fun r => hu r (Ψ r) fun W => ?_⟩
  exact RingHom.congr_fun (hΨ W) r

end GlobalTheory.AffGlue
