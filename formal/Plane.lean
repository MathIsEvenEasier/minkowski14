import Polygon
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

noncomputable section
namespace Minkowski14

/-- The real two-dimensional plane, equipped below with the fourteen-gon norm. -/
def Plane := ℂ

instance : AddCommGroup Plane := inferInstanceAs (AddCommGroup ℂ)
instance : Module ℝ Plane := inferInstanceAs (Module ℝ ℂ)

theorem plane_dimension : Module.finrank ℝ Plane = 2 :=
  Complex.finrank_real_complex

instance : NormedAddCommGroup Plane :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x : Plane => polygonNorm (show ℂ from x)
      map_zero' := map_zero polygonNorm
      add_le' := fun x y => map_add_le_add polygonNorm x y
      neg' := fun x => map_neg_eq_map polygonNorm x
      eq_zero_of_map_eq_zero' := fun x h => (polygonNorm_eq_zero x).mp h }

instance : NormedSpace ℝ Plane where
  norm_smul_le t x := le_of_eq (map_smul_eq_mul polygonNorm t x)

theorem plane_norm (x : Plane) : ‖x‖ = polygonNorm (show ℂ from x) := rfl

theorem plane_unit_ball (x : Plane) :
    ‖x‖ ≤ 1 ↔ (show ℂ from x) ∈ convexHull ℝ {z : ℂ | z^14=1} :=
  polygonNorm_le_one x

theorem plane_distance (x y : Plane) :
    dist x y = polygonNorm ((show ℂ from x) - (show ℂ from y)) := by
  rw [dist_eq_norm]
  rfl

end Minkowski14
