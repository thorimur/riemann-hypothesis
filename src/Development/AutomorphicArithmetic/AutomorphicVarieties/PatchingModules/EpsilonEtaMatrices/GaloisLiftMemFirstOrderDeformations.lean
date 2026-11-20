import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Parts

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}

private abbrev SS (n a : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ((p.1 : ℕ) < a ↔ (p.2 : ℕ) < a)}

private abbrev TT (n a : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ¬ ((p.1 : ℕ) < a ↔ (p.2 : ℕ) < a)}

private def upM (f : (SS n a → X) × (TT n a → Fin g → X)) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun i j => ⟨if h : i < j ∧ ((i : ℕ) < a ↔ (j : ℕ) < a) then f.1 ⟨(i, j), h⟩ else 0,
    if h : i < j ∧ ¬ ((i : ℕ) < a ↔ (j : ℕ) < a) then f.2 ⟨(i, j), h⟩ else 0, 0, 0⟩

end Parts
