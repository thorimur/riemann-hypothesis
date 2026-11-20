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
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace WAFrac

theorem galois_mem_den {R : Type*} [CommRing R] [IsDomain R] (g : R →+* R) {a b β γ T : R}
    (hgb : g b ≠ 0) (hrel : g a * b - a * g b = T * g b * b) (h : β * a = γ * b) :
    g β * a = (g γ - T * g β) * b := by
  have hg := congrArg g h
  rw [map_mul, map_mul] at hg
  refine mul_right_cancel₀ hgb ?_
  linear_combination b * hg - g β * hrel

theorem galois_sub_of_mul_eq {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (gR : R →+* R) (gS : S →+* S) (hfg : ∀ x, gS (f x) = f (gR x)) {a b T : R} {u : S}
    (hb : f b ≠ 0) (hgb : gS (f b) ≠ 0) (hrel : gR a * b - a * gR b = T * gR b * b) (hu : u * f b = f a) :
    gS u - u = f T := by
  have h1 : gS u * gS (f b) = f (gR a) := by rw [← map_mul, hu, hfg]
  have h2 := congrArg f hrel
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, ← hfg, ← hfg] at h2
  refine mul_right_cancel₀ hb (mul_right_cancel₀ hgb ?_)
  linear_combination f b * h1 - gS (f b) * hu + h2 - f b * hfg a

end WAFrac

end GroundTheory.PAdicHodge
