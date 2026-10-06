import Facet
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Minkowski14

/-- Six exact integer coefficients in the cyclotomic power basis. -/
structure Coordinate where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
  a5 : ℤ
  deriving DecidableEq, Inhabited

namespace Coordinate
noncomputable def eval (a : Coordinate) : ℂ :=
  a.a0 + a.a1*zeta + a.a2*zeta^2 + a.a3*zeta^3 + a.a4*zeta^4 + a.a5*zeta^5

def sub (a b : Coordinate) : Coordinate :=
  ⟨a.a0-b.a0,a.a1-b.a1,a.a2-b.a2,a.a3-b.a3,a.a4-b.a4,a.a5-b.a5⟩

theorem eval_sub (a b : Coordinate) : eval (sub a b) = eval a - eval b := by
  simp [eval, sub]; ring

def next (a : Coordinate) : Coordinate :=
  ⟨-a.a5, a.a0+a.a5, a.a1-a.a5, a.a2+a.a5, a.a3-a.a5, a.a4+a.a5⟩

theorem eval_next (a : Coordinate) : eval (next a) = zeta * eval a := by
  simp only [eval, next, Int.cast_neg, Int.cast_add, Int.cast_sub]
  linear_combination -(a.a5 : ℂ) * zeta_phi

def rotate : Nat → Coordinate → Coordinate
  | 0, a => a
  | n+1, a => next (rotate n a)

theorem eval_rotate (n : Nat) (a : Coordinate) : eval (rotate n a) = zeta^n * eval a := by
  induction n with
  | zero => simp [rotate]
  | succ n ih => rw [rotate, eval_next, ih, pow_succ']; ring
end Coordinate

noncomputable def parameterValue (p : ℤ × ℤ × ℤ) : ℝ := p.1 + p.2.1*rho + p.2.2*rho^2

def sideCoordinate (p : ℤ × ℤ × ℤ) : Coordinate :=
  let a:=p.1; let b:=p.2.1; let c:=p.2.2
  ⟨1+b-a-2*c,a+2*c-b,0,c,b-2*c,c⟩

theorem eval_sideCoordinate (p : ℤ × ℤ × ℤ) :
    Coordinate.eval (sideCoordinate p) =
      (1-parameterValue p) • (1:ℂ) + parameterValue p • zeta := by
  simp only [Coordinate.eval, sideCoordinate, parameterValue, Complex.real_smul,
    Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_intCast, Complex.ofReal_one, rho_complex]
  linear_combination ((p.2.1 : ℂ) + (p.2.2 : ℂ) *
    ((-2) * zeta^0 + (2) * zeta^2 + (1) * zeta^3 + (-1) * zeta^5)) * zeta_phi

end Minkowski14
