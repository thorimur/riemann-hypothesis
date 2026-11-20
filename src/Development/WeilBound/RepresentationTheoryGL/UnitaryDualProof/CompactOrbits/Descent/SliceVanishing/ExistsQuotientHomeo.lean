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
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace PositivityTheory.RgUd.T.Desc.SLF

open MulAction

variable {G T : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [TopologicalSpace T] [T2Space T] [BaireSpace T] [MulAction G T] [ContinuousSMul G T] [IsPretransitive G T]

theorem exists_quotient_homeo (t : T) :
    ∃ e : G ⧸ stabilizer G t ≃ₜ T, ∀ g : G, e (g : G ⧸ stabilizer G t) = g • t := by
  let f : G ⧸ stabilizer G t → T := ofQuotientStabilizer G t
  have hinj : Function.Injective f := injective_ofQuotientStabilizer G t
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := exists_smul_eq G t y
    exact ⟨(g : G ⧸ stabilizer G t), by simp [f, hg]⟩
  have hmk : ∀ g : G, f (g : G ⧸ stabilizer G t) = g • t := fun g => ofQuotientStabilizer_mk G t g
  have hcont : Continuous f := by
    rw [(QuotientGroup.isQuotientMap_mk (stabilizer G t)).continuous_iff]
    have : f ∘ (QuotientGroup.mk : G → G ⧸ stabilizer G t) = fun g => g • t := funext hmk
    rw [this]
    exact continuous_id.smul continuous_const
  have hopen : IsOpenMap f := by
    intro U hU
    have : f '' U = (fun g : G => g • t) '' ((QuotientGroup.mk : G → G ⧸ stabilizer G t) ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
        exact ⟨g, hc, (hmk g).symm⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨_, hg, hmk g⟩
    rw [this]
    exact isOpenMap_smul_of_sigmaCompact t _ (hU.preimage QuotientGroup.continuous_mk)
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen, hmk⟩

end PositivityTheory.RgUd.T.Desc.SLF
