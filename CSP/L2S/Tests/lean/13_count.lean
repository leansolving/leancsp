import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# Army counting

Find an army size in `100..800` leaving 2 soldiers over when counted in groups of 5,
2 over in groups of 7, and 1 over in groups of 12 — a system of three linear
congruences, expressed with `modulo` constraints.
-/

-- Complete CSP with modulo constraints
def army_problem : IntCSP :=
  ⟨1,  -- Single variable
   [ bound ⟨0, by decide⟩ 100 800,        -- Domain: 100..800
     modulo ⟨0, by decide⟩ 5 2,           -- army mod 5 = 2
     modulo ⟨0, by decide⟩ 7 2,           -- army mod 7 = 2
     modulo ⟨0, by decide⟩ 12 1           -- army mod 12 = 1
   ]⟩
