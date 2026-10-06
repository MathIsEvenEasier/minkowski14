import Polygon

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section
open Complex Set
open scoped Pointwise

namespace Minkowski14

def support : ℂ →ₗ[ℝ] ℝ where
  toFun z := (1 + zeta.re) * z.re + zeta.im * z.im
  map_add' x y := by simp [mul_add]; ring
  map_smul' t z := by simp; ring

theorem support_one : support 1 = 1 + zeta.re := by simp [support]

theorem support_zeta : support zeta = 1 + zeta.re := by
  have h := Complex.sq_norm zeta
  rw [norm_zeta] at h
  simp only [Complex.normSq_apply] at h
  simp [support]
  nlinarith

theorem support_eq (z : ℂ) :
    support z = z.re + ((starRingEnd ℂ) zeta * z).re := by
  simp [support, Complex.mul_re]
  ring

theorem star_zeta_mul : (starRingEnd ℂ) zeta * zeta = 1 := by
  rw [mul_comm, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, norm_zeta]

theorem power_re_le (j : ℕ) (hj0 : 0 < j) (hj14 : j < 14) :
    (zeta ^ j).re ≤ zeta.re := by
  have hj0' : (1 : ℝ) ≤ j := by exact_mod_cast hj0
  have hj14' : (j : ℝ) ≤ 13 := by exact_mod_cast (show j ≤ 13 by omega)
  have hc : zeta.re = Real.cos (Real.pi / 7) := by
    simpa using zeta_pow_re 1
  rw [hc, zeta_pow_re]
  by_cases hj7 : j ≤ 7
  · have hj7' : (j : ℝ) ≤ 7 := by exact_mod_cast hj7
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  · have hj8' : (8 : ℝ) ≤ j := by exact_mod_cast (show 8 ≤ j by omega)
    rw [← Real.cos_two_pi_sub ((j : ℝ) * Real.pi / 7)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]

theorem support_vertex_bound (z : ℂ) (hz : z ∈ vertices) :
    support z ≤ 1 + zeta.re := by
  obtain ⟨j, hj, rfl⟩ := zeta_primitive.eq_pow_of_pow_eq_one hz
  cases j with
  | zero => simp [support_one]
  | succ k =>
    rw [support_eq]
    have he : (starRingEnd ℂ) zeta * zeta ^ (k+1) = zeta ^ k := by
      rw [pow_succ', ← mul_assoc, star_zeta_mul, one_mul]
    rw [he]
    have ha := power_re_le (k+1) (by omega) hj
    have hb : (zeta ^ k).re ≤ 1 := by
      calc
        (zeta ^ k).re ≤ ‖zeta ^ k‖ := Complex.re_le_norm _
        _ = 1 := by simp [norm_pow, norm_zeta]
    linarith

theorem support_polygon_bound {z : ℂ} (hz : z ∈ polygon) :
    support z ≤ 1 + zeta.re := by
  exact convexHull_min (fun z hz => support_vertex_bound z hz)
    ((convex_Iic (1 + zeta.re)).linear_preimage support) hz

def multiply (w : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := w*z
  map_add' x y := mul_add w x y
  map_smul' t z := by simp [Complex.real_smul]; ring

theorem mul_mem_polygon {w z : ℂ} (hw : w ^ 14 = 1) (hz : z ∈ polygon) :
    w*z ∈ polygon := by
  apply convexHull_min (s := vertices) (t := (multiply w) ⁻¹' polygon)
    ?_ (polygon_convex.linear_preimage (multiply w)) hz
  intro v hv
  apply subset_convexHull ℝ vertices
  change (w*v)^14=1
  change v^14=1 at hv
  rw [mul_pow, hw, hv, one_mul]

theorem support_level_pos : 0 < 1 + zeta.re := by
  have hr : 0 < zeta.re := by
    have hc : zeta.re = Real.cos (Real.pi / 7) := by simpa using zeta_pow_re 1
    rw [hc]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  linarith

/-- Every point on every side has polygon norm exactly one. -/
theorem rotated_side_unit (w : ℂ) (hw : w ^ 14 = 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    polygonNorm (w * ((1-t) • (1:ℂ) + t • zeta)) = 1 := by
  let x := w * ((1-t) • (1:ℂ) + t • zeta)
  have hm : x ∈ polygon :=
    mul_mem_polygon hw (polygon_convex one_mem_polygon zeta_mem_polygon
      (by linarith) ht0 (by ring))
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hwi : (w⁻¹)^14=1 := by rw [inv_pow, hw, inv_one]
  have hx : support (w⁻¹*x) = 1+zeta.re := by
    change support (w⁻¹ * (w * ((1-t) • (1:ℂ) + t • zeta))) = _
    rw [← mul_assoc, inv_mul_cancel₀ hw0, one_mul, map_add, map_smul, map_smul,
      support_one, support_zeta]
    simp only [smul_eq_mul]
    ring
  apply le_antisymm (gauge_le_one_of_mem hm)
  change 1 ≤ gauge polygon x
  apply le_csInf polygon_absorbent.gauge_set_nonempty
  rintro r ⟨hr, y, hy, hxy⟩
  have hb := support_polygon_bound (mul_mem_polygon hwi hy)
  have he : support (w⁻¹*x) = r * support (w⁻¹*y) := by
    rw [← hxy]
    rw [mul_smul_comm, map_smul]
    rfl
  rw [hx] at he
  have hh := mul_le_mul_of_nonneg_left hb hr.le
  nlinarith [support_level_pos]

end Minkowski14
