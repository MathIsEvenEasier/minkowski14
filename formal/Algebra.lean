import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-! Exact algebraic coordinates for the regular tetradecagon.
The generator is defined by the standard complex exponential, so the
geometric interpretation does not depend on an unproved root selection. -/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section
open Complex

namespace Minkowski14

def zeta : ℂ := Complex.exp ((Real.pi : ℂ) * I / 7)

theorem zeta_primitive : IsPrimitiveRoot zeta 14 := by
  unfold zeta
  convert Complex.isPrimitiveRoot_exp 14 (by decide) using 1 <;>
    congr 1 <;> ring

theorem zeta_ne_zero : zeta ≠ 0 := Complex.exp_ne_zero _

theorem zeta_pow_seven : zeta ^ 7 = -1 := by
  rw [zeta, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring

theorem zeta_phi : zeta ^ 6 - zeta ^ 5 + zeta ^ 4 - zeta ^ 3 +
    zeta ^ 2 - zeta + 1 = 0 := by
  have hn : zeta + 1 ≠ 0 := by
    intro h
    have hz : zeta = -1 := by linear_combination h
    have h2 := zeta_primitive.pow_ne_one_of_pos_of_lt (by decide : 2 ≠ 0)
      (by decide : 2 < 14)
    exact h2 (by rw [hz]; norm_num)
  apply (mul_eq_zero.mp (show (zeta + 1) *
    (zeta ^ 6 - zeta ^ 5 + zeta ^ 4 - zeta ^ 3 + zeta ^ 2 - zeta + 1) = 0 by
      linear_combination zeta_pow_seven)).resolve_left hn

theorem norm_zeta : ‖zeta‖ = 1 := by
  simp [zeta, Complex.norm_exp]

def rho : ℝ := 2 * (zeta ^ 2).re

theorem rho_cos : rho = 2 * Real.cos (2 * Real.pi / 7) := by
  unfold rho zeta
  rw [← Complex.exp_nat_mul, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  congr 1 <;> ring

theorem rho_gt_one : 1 < rho := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ 2 * Real.pi / 7)
    (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi)
    (by linarith [Real.pi_pos] : 2 * Real.pi / 7 < Real.pi / 3)
  rw [Real.cos_pi_div_three] at h
  rw [rho_cos]
  linarith

theorem rho_complex : (rho : ℂ) = zeta ^ 2 - zeta ^ 5 := by
  have hc : zeta ^ 2 * (starRingEnd ℂ) (zeta ^ 2) = 1 := by
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, norm_pow, norm_zeta]
  have hc' : zeta ^ 2 * (-zeta ^ 5) = 1 := by
    linear_combination -zeta_pow_seven
  have he : (starRingEnd ℂ) (zeta ^ 2) = -zeta ^ 5 :=
    mul_left_cancel₀ (pow_ne_zero _ zeta_ne_zero) (hc.trans hc'.symm)
  calc
    (rho : ℂ) = zeta ^ 2 + (starRingEnd ℂ) (zeta ^ 2) := by
      apply Complex.ext <;> simp only [rho, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im] <;> norm_num <;> ring
    _ = zeta ^ 2 - zeta ^ 5 := by rw [he]; ring

theorem rho_cubic : rho ^ 3 + rho ^ 2 - 2 * rho - 1 = 0 := by
  have h : (rho : ℂ) ^ 3 + (rho : ℂ) ^ 2 - 2 * (rho : ℂ) - 1 = 0 := by
    rw [rho_complex]
    linear_combination ((-1) + (-1) * zeta + (-2) * zeta ^ 2 + (-2) * zeta ^ 3 + (1) * zeta ^ 4 + (3) * zeta ^ 5 + (3) * zeta ^ 6 + (-1) * zeta ^ 8 + (-1) * zeta ^ 9) * zeta_phi
  exact_mod_cast h

theorem cubic_strictMono :
    StrictMonoOn (fun x : ℝ => x ^ 3 + x ^ 2 - 2*x - 1) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx' : 1 ≤ x := hx
  have hy' : 1 ≤ y := hy
  have hp : 0 < x^2 + x*y + y^2 + x + y - 2 := by
    nlinarith [sq_nonneg (x-1), sq_nonneg y,
      mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ y)]
  have hm := mul_pos (sub_pos.mpr hxy) hp
  nlinarith

theorem rho_lower : (1246979603717467 : ℝ) / 10^15 < rho := by
  by_contra h
  have hm := cubic_strictMono.monotoneOn
    (show rho ∈ Set.Ici 1 from le_of_lt rho_gt_one)
    (show (1246979603717467 : ℝ) / 10^15 ∈ Set.Ici 1 by norm_num)
    (le_of_not_gt h)
  rw [rho_cubic] at hm
  norm_num at hm

theorem rho_upper : rho < (1246979603717468 : ℝ) / 10^15 := by
  by_contra h
  have hm := cubic_strictMono.monotoneOn
    (show (1246979603717468 : ℝ) / 10^15 ∈ Set.Ici 1 by norm_num)
    (show rho ∈ Set.Ici 1 from le_of_lt rho_gt_one)
    (le_of_not_gt h)
  rw [rho_cubic] at hm
  norm_num at hm

theorem zeta_pow_re (k : ℕ) : (zeta ^ k).re = Real.cos (k * Real.pi / 7) := by
  rw [zeta, ← Complex.exp_nat_mul, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  congr 1 <;> ring

theorem zeta_im_pos : 0 < zeta.im := by
  have h := Real.sin_pos_of_pos_of_lt_pi
    (by positivity : 0 < Real.pi / 7)
    (by linarith [Real.pi_pos] : Real.pi / 7 < Real.pi)
  simpa [zeta, Complex.exp_im, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im] using h

end Minkowski14
