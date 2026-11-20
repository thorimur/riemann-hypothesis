import Formalism.FockGram.FockGramProofs.FockHerm
import Formalism.FockGram.FockGramProofs.SubIndexNorm
import Formalism.FockGram.FockGramProofs.HermDualOf

namespace Formalism.E

theorem fockHerm : FockHerm := fischerInnerConjSymm_holds

theorem subIndexNorm : SubIndexNorm := indexEqNormDet

theorem hermDual : HermDual := hermDual_of subIndexNorm

end Formalism.E
