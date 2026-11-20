import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfinitePrimesNegIsSquare
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_primes_neg_square_padic : ∀ (q : ℕ) [Fact q.Prime], {p : ℕ | p.Prime ∧ IsSquare (-(p : ℚ_[q]))}.Infinite := by
  first | exact @GlobalTheory.RealGal.PrimesNegSquare.infinite_primes_neg_isSquare | exact GlobalTheory.RealGal.PrimesNegSquare.infinite_primes_neg_isSquare | (intros; apply GlobalTheory.RealGal.PrimesNegSquare.infinite_primes_neg_isSquare <;> assumption)
