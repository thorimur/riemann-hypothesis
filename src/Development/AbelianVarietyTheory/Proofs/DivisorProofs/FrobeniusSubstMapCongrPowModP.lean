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
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FrobCong

theorem frobenius_congr (p : ℕ) [hpf : Fact p.Prime] (B : Type) [CommRing B] (σB : B →+* B)
    (hσ : ∀ b, (p : B) ∣ σB b - b ^ p) (d : ℕ) (g : MvPowerSeries (Fin d) B) (α : Fin d →₀ ℕ) :
    (p : B) ∣ coeff α (subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) - g ^ p) := by
  have hp : p ≠ 0 := hpf.out.ne_zero
  set I : Ideal B := Ideal.span {(p : B)} with hI
  set π : B →+* B ⧸ I := Ideal.Quotient.mk I with hπ
  have hsub : subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g)
      = expand p hp (map σB g) := by
    rw [expand, substAlgHom_apply]
  rw [hsub, ← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ,
    ← coeff_map, map_sub, map_pow, map_expand, map_map]
  rcases subsingleton_or_nontrivial (B ⧸ I) with hs | hs
  · exact Subsingleton.elim _ _
  have hp0 : ((p : ℕ) : B ⧸ I) = 0 := by
    have h1 : π (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rwa [map_natCast] at h1
  haveI : CharP (B ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpf.out).2 hp0
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime hpf.out
  have hcomp : π.comp σB = (frobenius (B ⧸ I) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [hcomp, ← map_map, ← map_expand, map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCong
