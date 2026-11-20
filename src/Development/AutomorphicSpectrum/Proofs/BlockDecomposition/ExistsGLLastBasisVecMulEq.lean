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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.RowSect

theorem exists_GL_last_row (k : Type) [Field k] (m : ℕ) (ξ : Fin (m + 1) → k) (hξ : ξ ≠ 0) :
    ∃ h : GL (Fin (m + 1)) k,
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ᵥ* (h : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  classical
  have hs : LinearIndepOn k id ({ξ} : Set (Fin (m + 1) → k)) := (linearIndepOn_singleton_iff k).2 hξ
  have hmem : ξ ∈ hs.extend (Set.subset_univ _) := Module.Basis.subset_extend hs (Set.mem_singleton ξ)
  have hcard : Fintype.card (hs.extend (Set.subset_univ _)) = m + 1 := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.extend hs), Module.finrank_fin_fun]
  let e₀ := Fintype.equivFinOfCardEq hcard
  let e := e₀.trans (Equiv.swap (e₀ ⟨ξ, hmem⟩) (Fin.last m))
  have he : e.symm (Fin.last m) = ⟨ξ, hmem⟩ := by
    rw [Equiv.symm_apply_eq]
    simp [e]
  let b := (Module.Basis.extend hs).reindex e
  have hlast : b (Fin.last m) = ξ := by
    simp only [b, Module.Basis.reindex_apply, he, Module.Basis.extend_apply_self]
  have hu : IsUnit (Matrix.of fun i j => b i j) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 b.linearIndependent
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, single_vecMul, one_smul]
  exact hlast

end GlobalTheory.CompanionTheory.RowSect
