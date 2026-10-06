import MathIsEasy.Tactic.Sat.FromLRATStream

-- A satisfiable formula and a false claimed empty-clause derivation.
-- The input bundle must be accepted; the false LRAT step MUST be rejected.
run_cmd do
  liftM <| IO.FS.writeFile "/tmp/m14-negative.cnf" "p cnf 1 1\n1 0\n"
run_cmd do
  liftM <| IO.FS.writeFile "/tmp/m14-negative.lrat" "2 0 1 0\n"
namespace NegativeControlSAT
lrat_stream_context ctx "/tmp/m14-negative.cnf"
lrat_stream_inputs ctx certificate "/tmp/m14-negative.cnf" "/tmp/m14-negative.lrat"
lrat_stream_chunk ctx certificate 0 1 "/tmp/m14-negative.cnf" "/tmp/m14-negative.lrat"
end NegativeControlSAT
