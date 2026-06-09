import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Solving 20 Linear Equations (06_eq20)

This problem solves a system of 20 linear equations with 7 variables.
Each equation has the form: c₀*x[0] + c₁*x[1] + ... + c₆*x[6] = target

## Problem Details
- **Variables**: 7 variables (x[0]..x[6])
- **Domain**: 0..10 for all variables
- **Constraints**: 20 linear equations with large integer coefficients

## Source
Ported from Gecode example by Guido Tack
Original: 2007-02-22
-/

-- Helper to create a vector of coefficients from a list
def makeCoeffVector (n : ℕ) (coeffs : List ℤ) (h : coeffs.length = n) :
    _root_.Vector ℤ n :=
  ⟨coeffs.toArray, by simp [h]⟩

-- Helper to create variable scope (all variables)
def allVars (n : ℕ) : _root_.Vector (VarType n) n :=
  _root_.Vector.ofFn id

-- General function for creating a CSP with multiple linear equations
def linear_equations_csp (n_vars : ℕ) (lb ub : ℤ)
    (equations : List (List ℤ × ℤ)) :
    IntCSP :=
  let bounds_list := (List.finRange n_vars).map fun i => bound i lb ub
  let linear_constraints := equations.filterMap fun (coeffs, target) =>
    if h : coeffs.length = n_vars then
      some (linear_eq (allVars n_vars) (makeCoeffVector n_vars coeffs h) target)
    else
      none
  ⟨n_vars, bounds_list ++ linear_constraints⟩

-- The 20 linear equations from 06_eq20.mzn
-- Each tuple is (coefficients, target)
def eq20_equations : List (List ℤ × ℤ) := [
  ([-76706, 98205, 23445, 67921, 24111, -48614, -41906], 821228),
  ([87059, -29101, -5513, -21219, 22128, 7276, 57308], 22167),
  ([-60113, 29475, 34421, -76870, 62646, 29278, -15212], 251591),
  ([49149, 52871, -7132, 56728, -33576, -49530, -62089], 146074),
  ([-10343, 87758, -11782, 19346, 70072, -36991, 44529], 740061),
  ([85176, -95332, -1268, 57898, 15883, 50547, 83287], 373854),
  ([-85698, 29958, 57308, 48789, -78219, 4657, 34539], 249912),
  ([-67456, 84750, -51553, 21239, 81675, -99395, -4254], 277271),
  ([94016, -82071, 35961, 66597, -30705, -44404, -38304], 25334),
  ([-60301, 31227, 93951, 73889, 81526, -72702, 68026], 1410723),
  ([-16835, 47385, 97715, -12640, 69028, 76212, -81102], 1244857),
  ([-43277, 43525, 92298, 58630, 92590, -9372, -60227], 1503588),
  ([-64919, 80460, 90840, -59624, -75542, 25145, -47935], 18465),
  ([-45086, 51830, -4578, 96120, 21231, 97919, 65651], 1198280),
  ([85268, 54180, -18810, -48219, 6013, 78169, -79785], 90614),
  ([8874, -58412, 73947, 17147, 62335, 16005, 8632], 752447),
  ([71202, -11119, 73017, -38875, -14413, -29234, 72370], 129768),
  ([1671, -34121, 10763, 80609, 42532, 93520, -33488], 915683),
  ([51637, 67761, 95951, 3834, -96722, 59190, 15280], 533909),
  ([-16105, 62397, -6704, 43340, 95100, -68610, 58301], 876370)
]

-- Specific instance: solving the 20 linear equations
def eq20_problem : IntCSP :=
  let n := 7
  linear_equations_csp n 0 10 eq20_equations

def main : IO Unit := do
  saveAllBackendsAutoTimed eq20_problem
