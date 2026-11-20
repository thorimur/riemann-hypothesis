import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LaurentPolynomialCharacterIsMonomial
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentPolynomial_character_isMonomial : GlobalTheory.RegSS.CharacterMonomial := by
  first | exact @GlobalTheory.RegSS.characterMonomial | exact GlobalTheory.RegSS.characterMonomial | (intros; apply GlobalTheory.RegSS.characterMonomial <;> assumption)
