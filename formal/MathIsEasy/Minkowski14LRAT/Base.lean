import MathIsEasy.Tactic.Sat.FromLRATStream

namespace MathIsEasy.Minkowski14LRAT

lrat_stream_context ctx
  "artifacts/minkowski14_final_4color.cnf"

set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
    lrat_stream_inputs ctx certificate
      "artifacts/minkowski14_final_4color.cnf"
      "artifacts/minkowski14_final_4color.lrat"

end MathIsEasy.Minkowski14LRAT
