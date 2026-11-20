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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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

theorem UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (B : Type)
    [inst_2 : CommRing B] [inst_3 : Algebra k B] [Algebra.FiniteType k B] [IsReduced B] {c : B},
    c ≠ (0 : B) → ∃ (x : B →ₐ[k] k), (x : B → k) c ≠ (0 : k) := by
  intro k _ _ B _ _ _ _ c hc
  haveI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal B).IsRadical := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    exact (Ideal.mem_bot).2 (IsNilpotent.eq_zero ⟨n, (Ideal.mem_bot).1 hn⟩)
  have hj : (⊥ : Ideal B).jacobson = ⊥ := IsJacobsonRing.out ‹_› hrad
  have hcj : c ∉ (⊥ : Ideal B).jacobson := by
    rw [hj]
    exact fun h => hc ((Ideal.mem_bot).1 h)
  rw [Ideal.jacobson, Ideal.mem_sInf] at hcj
  push Not at hcj
  obtain ⟨m, ⟨-, hm⟩, hcm⟩ := hcj
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  let f : (B ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨f.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  intro h
  apply hcm
  have h1 : f (Ideal.Quotient.mk m c) = 0 := h
  have h2 : Ideal.Quotient.mk m c = 0 := (map_eq_zero f).1 h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2
