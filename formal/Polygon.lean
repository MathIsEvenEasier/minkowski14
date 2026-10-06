import Algebra

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 2000

noncomputable section
open Complex Set Filter
open scoped Topology Pointwise

namespace Minkowski14

/-- The vertices of the standard regular tetradecagon, independently of
the algebraic encoding used for the finite graph. -/
def vertices : Set ℂ := {z | z ^ 14 = 1}

def polygon : Set ℂ := convexHull ℝ vertices

theorem vertices_eq_range : vertices = Set.range (fun j : Fin 14 => zeta ^ j.val) := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj, he⟩ := zeta_primitive.eq_pow_of_pow_eq_one hz
    exact ⟨⟨j, hj⟩, he⟩
  · rintro ⟨j, rfl⟩
    change (zeta ^ j.val) ^ 14 = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, zeta_primitive.pow_eq_one, one_pow]

theorem polygon_convex : Convex ℝ polygon := convex_convexHull ℝ vertices

theorem polygon_compact : IsCompact polygon := by
  apply Set.Finite.isCompact_convexHull
  rw [vertices_eq_range]
  exact Set.finite_range _

theorem polygon_neg : -polygon = polygon := by
  have h : -vertices = vertices := by
    ext z
    simp only [Set.mem_neg, vertices, Set.mem_ofPred_eq]
    rw [neg_pow]
    norm_num
  unfold polygon
  rw [← convexHull_neg, h]

theorem polygon_balanced : Balanced ℝ polygon := by
  apply (balanced_iff_neg_mem polygon_convex).mpr
  intro z hz
  rw [← polygon_neg]
  exact neg_mem_neg.mpr hz

theorem one_mem_polygon : (1 : ℂ) ∈ polygon :=
  subset_convexHull ℝ vertices (by simp [vertices])

theorem zeta_mem_polygon : zeta ∈ polygon :=
  subset_convexHull ℝ vertices zeta_primitive.pow_eq_one

theorem zero_mem_polygon : (0 : ℂ) ∈ polygon := by
  simpa using polygon_balanced.smul_mem (a := (0 : ℝ)) (by simp) one_mem_polygon

theorem polygon_absorbent : Absorbent ℝ polygon := by
  apply absorbent_iff_eventually_nhdsNE_zero.mpr
  intro z
  let a : ℝ := z.re - z.im * zeta.re / zeta.im
  let b : ℝ := z.im / zeta.im
  have hz : z = a • (1 : ℂ) + b • zeta := by
    apply Complex.ext <;> simp [a, b, Complex.mul_re, Complex.mul_im] <;>
      field_simp [ne_of_gt zeta_im_pos] <;> ring
  have ha : Tendsto (fun t : ℝ => ‖t * (2*a)‖) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_id.mul continuous_const).norm.continuousAt.tendsto :
      Tendsto (fun t : ℝ => ‖t * (2*a)‖) (𝓝 0) (𝓝 ‖(0:ℝ)*(2*a)‖))
  have hb : Tendsto (fun t : ℝ => ‖t * (2*b)‖) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_id.mul continuous_const).norm.continuousAt.tendsto :
      Tendsto (fun t : ℝ => ‖t * (2*b)‖) (𝓝 0) (𝓝 ‖(0:ℝ)*(2*b)‖))
  have ha' := (ha.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  have hb' := (hb.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  filter_upwards [ha', hb'] with t hta htb
  have hx := polygon_balanced.smul_mem (le_of_lt hta) one_mem_polygon
  have hy := polygon_balanced.smul_mem (le_of_lt htb) zeta_mem_polygon
  have hm := polygon_convex hx hy (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
  convert hm using 1
  rw [hz]
  simp only [smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- The Minkowski functional of the regular fourteen-gon. -/
def polygonNorm : Seminorm ℝ ℂ :=
  gaugeSeminorm polygon_balanced polygon_convex polygon_absorbent

theorem polygonNorm_apply (z : ℂ) : polygonNorm z = gauge polygon z := rfl

theorem polygonNorm_eq_zero (z : ℂ) : polygonNorm z = 0 ↔ z = 0 := by
  exact gauge_eq_zero polygon_absorbent (polygon_compact.isVonNBounded ℝ)

theorem polygonNorm_le_one (z : ℂ) : polygonNorm z ≤ 1 ↔ z ∈ polygon := by
  constructor
  · intro hz
    have h := mem_closure_of_gauge_le_one polygon_convex zero_mem_polygon polygon_absorbent hz
    rwa [polygon_compact.isClosed.closure_eq] at h
  · exact gauge_le_one_of_mem

end Minkowski14
