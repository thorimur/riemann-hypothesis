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

namespace Zc.Comb

universe u

structure ASeg (T : Type u) where
  start : T
  len : ℕ
  len_pos : 0 < len

variable {T : Type u}

def ASeg.carrier (s : T → T) (Δ : ASeg T) : Set T := {t | ∃ i < Δ.len, s^[i] Δ.start = t}

def ASeg.dec (s : T → T) (Δ : ASeg T) : List T := (List.range Δ.len).reverse.map fun i => s^[i] Δ.start

def ALinked (s : T → T) (Δ Δ' : ASeg T) : Prop :=
  (∃ Γ : ASeg T, Γ.carrier s = Δ.carrier s ∪ Δ'.carrier s) ∧ ¬ Δ.carrier s ⊆ Δ'.carrier s ∧
    ¬ Δ'.carrier s ⊆ Δ.carrier s

def APrecedes (s : T → T) (Δ Δ' : ASeg T) : Prop :=
  ALinked s Δ Δ' ∧ ∃ j : ℕ, 0 < j ∧ Δ'.start = s^[j] Δ.start

def AOrdered (s : T → T) (L : List (ASeg T)) : Prop := L.Pairwise fun a b => ¬ APrecedes s a b

def wt (s : T → T) (L : List (ASeg T)) : List T := (L.reverse.map (ASeg.dec s)).flatten

inductive Interleave : List T → List T → List T → Prop
  | nil : Interleave [] [] []
  | left {a : T} {u v w : List T} : Interleave u v w → Interleave (a :: u) v (a :: w)
  | right {a : T} {u v w : List T} : Interleave u v w → Interleave u (a :: v) (a :: w)

inductive Shuffle : List (List T) → List T → Prop
  | nil : Shuffle [] []
  | cons {u : List T} {us : List (List T)} {v w : List T} : Shuffle us v → Interleave u v w → Shuffle (u :: us) w

def InSh (s : T → T) (m : Multiset (ASeg T)) (w : List T) : Prop :=
  ∃ L : List (ASeg T), (L : Multiset (ASeg T)) = m ∧ Shuffle (L.map (ASeg.dec s)) w

def sqLen (m : Multiset (ASeg T)) : ℕ := (m.map fun Δ => Δ.len ^ 2).sum

end Zc.Comb
