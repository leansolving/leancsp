import CSP.L2S.Backends.PB.Extend

namespace CSP.L2S.PB

open CSPSig

/-!
# PB backend — composable per-constraint soundness (`EncConstr`) and the general
  `CSP-SAT ⇒ PB-SAT` composition theorem

`Extend.lean`'s `csp_unsat_generic` leaves the central soundness obligation
(`hsound`) as a hypothesis that each instance discharges by hand.  This file packages
that obligation **per constraint** and composes a list of them into a single
assumption-free theorem.

* `EncConstr S` bundles, for one encoded constraint: the PB constraints it
  contributes (`constrs`), its arithmetic precondition on the integer assignment
  (`pre`), the auxiliary variables it owns and how to set them (`setsAux`), and a
  `sound` proof that — in-domain, with its precondition and its own aux indices set
  correctly — every contributed constraint holds on `extend`.  Aux-free constraints
  use `setsAux _ = []`; their `sound` ignores the (vacuous) frame hypothesis.
* `csp_unsat_of_enc` — the general spine: given a list of `EncConstr`, a global
  `auxOf` agreeing with each entry's `setsAux`, and a `formulaUnsat` certificate over
  the combined formula, no in-domain assignment satisfies all the preconditions.
  This is the assumption-free `CSP-SAT ⇒ PB-SAT` theorem.
* `csp_unsat_of_encfree` — the aux-free convenience wrapper (`auxOf := false`).
* `globalAuxOf` / `csp_unsat_of_enc_alloc` — the **aux allocator**: with pairwise
  distinct owned aux indices, the global `auxOf` is built automatically (by lookup),
  so arbitrarily many aux-using constraints compose.  The disjointness obligation is
  `decide`-able when the owned indices are static.

The trust base is unchanged: every `sound` reuses already-verified `extend_sat_*`
lemmas, and the certificate still rides through PBLean's checker, discharged by a
`Lean.ofReduceBool` term.
-/

variable {S : CSPSig}

/-- A soundness-carrying encoded constraint over a fixed signature `S`. -/
structure EncConstr (S : CSPSig) where
  /-- The PB constraints this entry contributes to the combined formula. -/
  constrs : List (PBConstr (PBVar S))
  /-- The arithmetic precondition this entry needs from the integer assignment. -/
  pre : (Fin S.nInt → Int) → Prop
  /-- The auxiliary indices this entry owns, paired with the value each must take
      (as a function of the assignment).  Aux-free entries use `fun _ => []`. -/
  setsAux : (Fin S.nInt → Int) → List (Fin S.nAux × Bool)
  /-- Soundness: in-domain, with `pre` and this entry's own aux indices set as
      `setsAux` dictates, every contributed constraint holds on `extend`.  The frame
      hypothesis mentions only this entry's indices, so entries compose. -/
  sound : ∀ (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool) (auxA : Fin S.nAux → Bool),
    (∀ i, a i ∈ S.values i) → pre a →
    (∀ p ∈ setsAux a, auxA p.1 = p.2) →
    ∀ c ∈ constrs, c.sat (extend a bA auxA)

/-- The combined PB constraint list of a list of encoded constraints. -/
def EncConstr.combine (es : List (EncConstr S)) : List (PBConstr (PBVar S)) :=
  es.flatMap (·.constrs)

/-- **General composition (`CSP-SAT ⇒ PB-SAT`).**  Given a list of encoded
    constraints, a global aux assignment `auxOf` agreeing with every entry's
    `setsAux`, and a `formulaUnsat` certificate over the order-encoding staircase plus
    the combined constraints, no in-domain assignment satisfies all the preconditions. -/
theorem csp_unsat_of_enc (S : CSPSig) (es : List (EncConstr S))
    (auxOf : (Fin S.nInt → Int) → (Fin S.nBool → Bool) → (Fin S.nAux → Bool))
    (haux : ∀ a bA, ∀ e ∈ es, ∀ p ∈ e.setsAux a, auxOf a bA p.1 = p.2)
    (hunsat : VeriPB.Reflect.formulaUnsat
      ((S.monotonicity ++ EncConstr.combine es).toArray.map PBConstr.toNatConstr)) :
    ¬ ∃ (a : Fin S.nInt → Int), (∀ i, a i ∈ S.values i) ∧ ∀ e ∈ es, e.pre a := by
  rintro ⟨a, hdom, hpre⟩
  refine csp_unsat_generic S (EncConstr.combine es)
    (fun a _ => ∀ e ∈ es, e.pre a) auxOf ?_ hunsat ⟨a, fun _ => false, hdom, hpre⟩
  intro a' bA hdom' hpre' c hc
  simp only [EncConstr.combine, List.mem_flatMap] at hc
  obtain ⟨e, he, hce⟩ := hc
  exact e.sound a' bA (auxOf a' bA) hdom' (hpre' e he)
    (fun p hp => haux a' bA e he p hp) c hce

/-- **Aux-free composition.**  Specialization of `csp_unsat_of_enc` with `auxOf`
    constantly `false`; the entries' `setsAux` must be empty (so the `haux`
    obligation is vacuous). -/
theorem csp_unsat_of_encfree (S : CSPSig) (es : List (EncConstr S))
    (hfree : ∀ a, ∀ e ∈ es, e.setsAux a = [])
    (hunsat : VeriPB.Reflect.formulaUnsat
      ((S.monotonicity ++ EncConstr.combine es).toArray.map PBConstr.toNatConstr)) :
    ¬ ∃ (a : Fin S.nInt → Int), (∀ i, a i ∈ S.values i) ∧ ∀ e ∈ es, e.pre a := by
  refine csp_unsat_of_enc S es (fun _ _ _ => false) ?_ hunsat
  intro a bA e he p hp
  rw [hfree a e he] at hp
  simp at hp

/-! ### The aux allocator -/

/-- With pairwise-distinct keys, looking up any present pair returns its value. -/
theorem lookup_of_nodup_mem {α : Type} [DecidableEq α] {β : Type}
    (L : List (α × β)) (p : α × β)
    (hnd : (L.map Prod.fst).Nodup) (hp : p ∈ L) : L.lookup p.1 = some p.2 := by
  induction L with
  | nil => simp at hp
  | cons q t ih =>
    obtain ⟨qk, qv⟩ := q
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hq, hndt⟩ := hnd
    rcases List.mem_cons.mp hp with rfl | hpt
    · simp
    · have hmem : p.1 ∈ t.map Prod.fst := List.mem_map.mpr ⟨p, hpt, rfl⟩
      have hne : (p.1 == qk) = false := by
        rw [beq_eq_false_iff_ne]; intro h; exact hq (h ▸ hmem)
      rw [List.lookup_cons, hne]
      exact ih hndt hpt

/-- The global aux assignment built by looking each index up among all entries'
    owned (index, value) pairs; indices nobody owns default to `false`. -/
def globalAuxOf (es : List (EncConstr S))
    (a : Fin S.nInt → Int) (_bA : Fin S.nBool → Bool) : Fin S.nAux → Bool :=
  fun s => ((es.flatMap (·.setsAux a)).lookup s).getD false

/-- **Aux allocator composition.**  If across all entries the owned aux indices are
    pairwise distinct, the global `auxOf` is constructed automatically, so no manual
    aux-setter is needed.  The disjointness hypothesis is `decide`-able when the owned
    indices are static (independent of `a`), which is the case for every encoder. -/
theorem csp_unsat_of_enc_alloc (S : CSPSig) (es : List (EncConstr S))
    (hnd : ∀ a, ((es.flatMap (·.setsAux a)).map Prod.fst).Nodup)
    (hunsat : VeriPB.Reflect.formulaUnsat
      ((S.monotonicity ++ EncConstr.combine es).toArray.map PBConstr.toNatConstr)) :
    ¬ ∃ (a : Fin S.nInt → Int), (∀ i, a i ∈ S.values i) ∧ ∀ e ∈ es, e.pre a := by
  refine csp_unsat_of_enc S es (globalAuxOf es) ?_ hunsat
  intro a bA e he p hp
  have hmem : p ∈ es.flatMap (·.setsAux a) := List.mem_flatMap.mpr ⟨e, he, hp⟩
  have hlk := lookup_of_nodup_mem _ p (hnd a) hmem
  simp only [globalAuxOf, hlk, Option.getD_some]

end CSP.L2S.PB
