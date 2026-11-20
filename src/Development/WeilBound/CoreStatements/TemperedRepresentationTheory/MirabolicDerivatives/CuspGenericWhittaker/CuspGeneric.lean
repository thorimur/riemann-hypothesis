import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Matrix

namespace GlobalTheory.BZMir.Whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def WhitLeOne : Prop :=
  ∀ (n : ℕ) (ψ : AddChar k Circle) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → Continuous ψ → ψ ≠ 1 →
      Module.rank ℂ (TwJacquet π (unipB k (Fin n)) (whitChar ψ n)) ≤ 1

def WhitCusp : Prop :=
  ∀ (n : ℕ) (ψ : AddChar k Circle) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → IsCuspidal π → 0 < n → Continuous ψ → ψ ≠ 1 →
      Module.rank ℂ (TwJacquet π (unipB k (Fin n)) (whitChar ψ n)) = 1

def CuspGeneric : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → IsCuspidal π → 0 < n → IsGeneric π

end GlobalTheory.BZMir.Whit

end
