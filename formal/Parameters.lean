import Coordinates
set_option linter.unusedSimpArgs false
noncomputable section
namespace Minkowski14

def parameter : Nat → ℤ × ℤ × ℤ
  | 0 => ((-4), 0, 3)
  | 1 => ((-4), 1, 2)
  | 2 => ((-3), (-1), 3)
  | 3 => ((-3), 0, 2)
  | 4 => ((-2), (-3), 4)
  | 5 => ((-2), (-2), 3)
  | 6 => ((-2), 1, 1)
  | 7 => ((-2), 2, 0)
  | 8 => ((-1), (-1), 2)
  | 9 => ((-1), 0, 1)
  | 10 => ((-1), 1, 0)
  | 11 => (0, (-2), 2)
  | 12 => (0, (-1), 1)
  | 13 => (0, 2, (-1))
  | 14 => (0, 3, (-2))
  | 15 => (1, (-3), 2)
  | 16 => (1, (-2), 1)
  | 17 => (1, 0, 0)
  | 18 => (1, 1, (-1))
  | 19 => (1, 2, (-2))
  | 20 => (2, (-1), 0)
  | 21 => (2, 0, (-1))
  | 22 => (2, 1, (-2))
  | 23 => (3, (-1), (-1))
  | 24 => (3, 2, (-3))
  | 25 => (3, 3, (-4))
  | 26 => (4, 0, (-2))
  | 27 => (4, 1, (-3))
  | 28 => (4, 2, (-4))
  | _ => (0,0,0)

theorem parameter_bounds (n : Nat) :
    0 ≤ parameterValue (parameter n) ∧ parameterValue (parameter n) ≤ 1 := by
  have h0 := rho_lower
  have h1 := rho_upper
  have h2 : (1246979603717467 / 1000000000000000 : ℝ)^2 < rho^2 := by nlinarith [rho_gt_one]
  have h3 : rho^2 < (1246979603717468 / 1000000000000000 : ℝ)^2 := by nlinarith [rho_gt_one]
  have hr : 0 < rho := by linarith [rho_gt_one]
  unfold parameter parameterValue
  split <;> norm_num [abs_of_pos hr] <;> constructor <;> nlinarith

def unitCoordinate (k : Nat) : Coordinate :=
  Coordinate.rotate (k % 14) (sideCoordinate (parameter (k / 14)))

theorem unitCoordinate_norm (k : Nat) : polygonNorm (Coordinate.eval (unitCoordinate k)) = 1 := by
  rw [unitCoordinate, Coordinate.eval_rotate, eval_sideCoordinate]
  apply rotated_side_unit
  · rw [← pow_mul, Nat.mul_comm, pow_mul, zeta_primitive.pow_eq_one, one_pow]
  · exact (parameter_bounds (k/14)).1
  · exact (parameter_bounds (k/14)).2

end Minkowski14
