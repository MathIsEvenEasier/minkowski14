import MathIsEasy.Tactic.Sat.FromLRATStream

run_cmd do
  liftM <| IO.FS.writeFile "/tmp/m14-positive.cnf" "p cnf 1 2\n1 0\n-1 0\n"
run_cmd do
  liftM <| IO.FS.writeFile "/tmp/m14-positive.lrat" "3 0 1 2 0\n"
namespace PositiveControl
lrat_stream_context ctx "/tmp/m14-positive.cnf"
lrat_stream_inputs ctx certificate "/tmp/m14-positive.cnf" "/tmp/m14-positive.lrat"
lrat_stream_chunk ctx certificate 0 1 "/tmp/m14-positive.cnf" "/tmp/m14-positive.lrat"
#print axioms certificate.clause_3
end PositiveControl
