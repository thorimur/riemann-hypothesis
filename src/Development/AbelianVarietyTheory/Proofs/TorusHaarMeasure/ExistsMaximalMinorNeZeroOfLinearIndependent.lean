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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in

theorem _root_.GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent
    (K : Type) [Field K] (r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → K)
    (hw : LinearIndependent K w) :
    ∃ e : ι → Fin r, Function.Injective e ∧ (Matrix.of fun k a => w a (e k)).det ≠ 0 := by
  classical
  set A : Matrix (Fin r) ι K := Matrix.of fun k a => w a k with hA
  have hcol : A.col = w := rfl
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_cols, hcol, finrank_span_eq_card hw]
  have htop : Submodule.span K (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  haveI : Fintype κ := Fintype.ofInjective a ha
  let b := Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K), Module.finrank_eq_card_basis b]
  let f : ι ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ f, ha.comp f.injective, ?_⟩
  have hrow : LinearIndependent K (Matrix.of fun k a' => w a' ((a ∘ f) k)).row :=
    hli.comp f f.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrow)).ne_zero

end GlobalTheory
