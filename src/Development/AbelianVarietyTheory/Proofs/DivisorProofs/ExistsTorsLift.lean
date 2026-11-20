import Batteries.Data.Nat.Gcd
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.TateTransportAlg

theorem exists_torsLift {G H : Type} [Group G] [Group H] (p : ℕ) (ρ : G →* H)
    (hi : ∀ n, 0 < n → n.Coprime p → ∀ g h : G, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) :
    ∃ L : H → G, ∀ n, 0 < n → n.Coprime p → ∀ g : G, g ^ n = 1 → L (ρ g) = g := by
  classical
  refine ⟨fun x => if h : ∃ g : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g ^ n = 1) ∧ ρ g = x then h.choose else 1, ?_⟩
  intro n hn hnp g hg
  have h : ∃ g' : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g' ^ n = 1) ∧ ρ g' = ρ g := ⟨g, ⟨n, hn, hnp, hg⟩, rfl⟩
  simp only [dif_pos h]
  obtain ⟨⟨m, hm, hmp, hgm⟩, he⟩ := h.choose_spec
  exact hi (m * n) (Nat.mul_pos hm hn) (Nat.Coprime.mul hmp hnp) _ _
    (by rw [pow_mul, hgm, one_pow]) (by rw [mul_comm, pow_mul, hg, one_pow]) he

end GlobalTheory.TateTransportAlg
