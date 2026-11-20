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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.detFactor :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Matrix (Fin n) (Fin n) K),
      ∃ z : Fin n → K, ∀ c : K, (c • S - 1).det = ∏ i, (c * z i - 1) := by
  intro K _ _ n S
  classical
  set p := S.charpoly with hp
  have hmon : p.Monic := Matrix.charpoly_monic S
  have hprod : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod = p :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon IsAlgClosed.card_roots_eq_natDegree
  have hcard : Multiset.card p.roots = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have heval : ∀ x : K, (Matrix.scalar (Fin n) x - S).det = (p.roots.map (fun a => x - a)).prod := by
    intro x
    rw [← Matrix.eval_charpoly, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hz : ∃ z : Fin n → K, ∀ f : K → K, (p.roots.map f).prod = ∏ i, f (z i) := by
    obtain ⟨L, hL⟩ : ∃ L : List K, (L : Multiset K) = p.roots := ⟨_, Multiset.coe_toList _⟩
    have hlen : L.length = n := by rw [← hcard, ← hL, Multiset.coe_card]
    refine ⟨fun i => L.get (Fin.cast hlen.symm i), fun f => ?_⟩
    rw [← hL, Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp [hlen]
  obtain ⟨z, hz⟩ := hz
  refine ⟨z, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc
    simp [Matrix.det_neg]
  · have hmat : c • S - 1 = (-c) • (Matrix.scalar (Fin n) c⁻¹ - S) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.sub_apply, Matrix.one_apply]
        field_simp
        ring
      · simp [Matrix.sub_apply, Matrix.one_apply, hij]
    rw [hmat, Matrix.det_smul, heval, hz, Fintype.card_fin, ← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    field_simp
    ring
