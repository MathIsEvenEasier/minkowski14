import MathIsEasy.Minkowski14LRAT.Chunk041

namespace MathIsEasy.Minkowski14LRAT

set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
    lrat_stream_chunk ctx certificate 306567 307680
      "artifacts/minkowski14_final_4color.cnf"
      "artifacts/minkowski14_final_4color.lrat"

/-- The LRAT certificate derives the empty clause from the CNF. -/
theorem fourColouringCNFUnsatisfiable :
    _root_.Sat.Fmla.proof ctx _root_.Sat.Clause.nil :=
  certificate.clause_382792

end MathIsEasy.Minkowski14LRAT
