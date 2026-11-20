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
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

universe u_1

namespace Bl.AddValuationProducts

private lemma addVal_prod_alt {O : Type u_1} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type} (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

theorem goal1 :
  ∀ {O : Type u_1} [inst : CommRing.{u_1} O] [inst_1 : IsDomain.{u_1} O] [inst_2 : IsDiscreteValuationRing.{u_1} O]
  {ι : Type} [Fintype.{0} ι] [DecidableEq.{1} ι] (N : Submodule.{u_1, u_1} O (ι → O))
  (e :
    LinearEquiv.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} O) (ι → O)
      (Subtype.{u_1 + 1} fun (x : ι → O) ↦ Membership.mem.{u_1, u_1} N x)),
  Eq.{1} (Module.length.{u_1, u_1} O (HasQuotient.Quotient.{u_1, u_1} (ι → O) N))
    (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
      (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} LinearMap.det.{u_1, u_1}
        (LinearMap.comp.{u_1, u_1, u_1, u_1, u_1, u_1} (Submodule.subtype.{u_1, u_1} N)
          (LinearEquiv.toLinearMap.{u_1, u_1, u_1, u_1} e)))) := by
  intro O _ _ _ ι _ _ N e
  let b := Pi.basisFun O ι
  have h : Module.finrank O N = Module.finrank O (ι → O) := e.finrank_eq.symm
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : ι → O) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  have hL : Module.length O ((ι → O) ⧸ N) = ∑ i, IsDiscreteValuationRing.addVal O (a i) := by
    rw [(N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Ring.ord_eq_addVal (a i)
  let u : (ι → O) ≃ₗ[O] N := b'.equiv ab (Equiv.refl ι)
  have hgj : ∀ j, (N.subtype ∘ₗ u.toLinearMap) (b' j) = a j • b' j := by
    intro j
    rw [← hab j]
    simp [u]
  have hg : LinearMap.toMatrix b' b' (N.subtype ∘ₗ u.toLinearMap) = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, hgj, map_smul, Module.Basis.repr_self, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hdet : LinearMap.det (N.subtype ∘ₗ u.toLinearMap) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', hg, Matrix.det_diagonal]
  have hfac : N.subtype ∘ₗ e.toLinearMap =
      (N.subtype ∘ₗ u.toLinearMap) ∘ₗ (e.trans u.symm).toLinearMap := by
    ext x
    simp
  rw [hfac, LinearMap.det_comp, hdet, IsDiscreteValuationRing.addVal_mul, addVal_prod_alt,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 (LinearEquiv.isUnit_det' _), add_zero, hL]

end Bl.AddValuationProducts
