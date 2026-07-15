import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# Army Counting Problem with Modulo Constraints

## Problem Description
Find the size of an army where:
- The army size is between 100 and 800
- When counted in groups of 5, there are 2 soldiers left over
- When counted in groups of 7, there are 2 soldiers left over
- When counted in groups of 12, there is 1 soldier left over

## CSP Formulation
- **Variable**: 1 variable (army size)
- **Domain**: 100..800
- **Constraints**: Three modulo constraints
  - army mod 5 = 2
  - army mod 7 = 2
  - army mod 12 = 1

## Mathematical Analysis
This is a system of linear congruences. The solution must satisfy:
- army ≡ 2 (mod 5)
- army ≡ 2 (mod 7)
- army ≡ 1 (mod 12)

## Source
Classic puzzle - counting soldiers problem
-/

-- Complete CSP with modulo constraints
def army_problem : IntCSP :=
  ⟨1,  -- Single variable
   [ bound ⟨0, by decide⟩ 100 800,        -- Domain: 100..800
     modulo ⟨0, by decide⟩ 5 2,           -- army mod 5 = 2
     modulo ⟨0, by decide⟩ 7 2,           -- army mod 7 = 2
     modulo ⟨0, by decide⟩ 12 1           -- army mod 12 = 1
   ]⟩
