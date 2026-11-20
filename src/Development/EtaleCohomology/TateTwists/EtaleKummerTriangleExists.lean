import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKummerTriangleExists : Prop :=
  ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)
