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
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.Radical.NatInt
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

namespace GlobalTheory

theorem irreducible_idempotent_eq_one_and_character_eq_weight
    (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (ρ : Representation L G V) (hρ : ρ.IsIrreducible) :
    (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧
    (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) →
      ∀ g, ρ.character g = (lam g : L)) := by
  have key : ∀ (W : Submodule L V), (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W ≠ ⊥ → W = ⊤ := by
    intro W hW hne
    let S : Subrepresentation ρ := ⟨W, fun g x hx => hW g x hx⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hne
    · exact congrArg Subrepresentation.toSubmodule h
  refine ⟨fun e he hee hc => ?_, fun lam v hv hl g => ?_⟩
  · have h : LinearMap.range e = ⊤ := by
      refine key _ ?_ ?_
      · rintro g _ ⟨u, rfl⟩
        exact ⟨ρ g u, (congrArg (fun f : Module.End L V => f u) (hc g)).symm⟩
      · intro h
        exact he (LinearMap.range_eq_bot.mp h)
    ext w
    obtain ⟨u, rfl⟩ := LinearMap.range_eq_top.mp h w
    exact congrArg (fun f : Module.End L V => f u) hee
  · have h : Submodule.span L {v} = ⊤ := by
      refine key _ ?_ ?_
      · intro g x hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hl]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      · simpa using hv
    have hfin : Module.finrank L V = 1 := by
      rw [← finrank_top, ← h]
      exact finrank_span_singleton hv
    have hg : ρ g = (lam g : L) • LinearMap.id := by
      ext x
      have hx : x ∈ Submodule.span L {v} := h ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hl, smul_comm c]
    simp [Representation.character, hg, hfin]

end GlobalTheory
