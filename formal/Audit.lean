import Final
import FoundationAudit

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

assert_foundations Minkowski14.plane_unit_ball
assert_foundations Minkowski14.plane_dimension
assert_foundations Minkowski14.at_least_five_colours

#print axioms Minkowski14.zeta_primitive
#print axioms Minkowski14.rho_lower
#print axioms Minkowski14.rho_upper
#print axioms Minkowski14.polygonNorm_eq_zero
#print axioms Minkowski14.polygonNorm_le_one
#print axioms Minkowski14.rotated_side_unit
#print axioms Minkowski14.Coordinate.eval_rotate
#print axioms Minkowski14.eval_sideCoordinate
#print axioms Minkowski14.parameter_bounds
#print axioms Minkowski14.edges_unit
#print axioms MathIsEasy.Minkowski14.FinalGraph.notFourColourable
#print axioms Minkowski14.plane_unit_ball
#print axioms Minkowski14.plane_dimension

#check Minkowski14.plane_no_four_colouring
#check Minkowski14.plane_unit_ball
#check Minkowski14.at_least_five_colours
