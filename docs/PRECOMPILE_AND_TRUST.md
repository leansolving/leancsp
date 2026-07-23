# Precompiling the PB checker: how bv_decide does it, why PBLean doesn't, and what LeanCSP gains

Why Lean's built-in `bv_decide` runs its certificate checker as fast native code, why PBLean (the
pseudo-Boolean checker we use) runs the *same kind* of checker slowly through an interpreter, why
one build flag fixes that, and what it means for trust and for LeanCSP.

---

## 1. Background: two ways to "run a checker"

Both `bv_decide` and PBLean prove things by **reflection**:

1. Write a **checker**: a Lean function `f` taking a certificate, returning `true`/`false`.
2. **Prove once, in the kernel**, that it's *sound*: `f cert = true → the statement is really
   true`. This is normal, fully-trusted mathematics.
3. To prove an instance, **run** `f cert`. If it returns `true`, soundness gives the theorem.

The only interesting question is **how step 3 runs `f`**:

| Engine | How it runs `f` | Speed | Trust |
|---|---|---|---|
| **Interpreter** | walks `f`'s compiled instructions one at a time | slow | the Lean compiler |
| **Native code** | the CPU runs `f`'s machine code directly | fast | the Lean compiler (plus a little more — §4) |

Both engines run the **compiled** form of `f` (*compiled reflection*), so both put the compiler in
the trusted base. The **kernel** could also compute `f cert` itself, with zero compiler trust, but
it is far too slow for large certificates.

Which engine you get is **not** a property of `f`'s source code. It's a **build decision**: is
native machine code for `f` loaded when we run it?

---

## 2. bv_decide: native by default, and why

`bv_decide` checks LRAT certificates from an external SAT solver (CaDiCaL). Its checker is native
out of the box for one reason: it lives **inside the Lean toolchain**, which ships already
compiled. You can see the machine code in the shared library every Lean process loads:

```
$ nm -D lib/lean/libleanshared.so | grep compactLratChecker
... Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go ...
```

So the evaluator just jumps straight to it. (Mechanically: `bv_decide` compiles two small helper
definitions — the reflected goal and the certificate — applies the library function `verifyBVExpr`
to them, runs that natively, and turns "the check returned `true`" into a proof; §4 covers by
which mechanism.)

**bv_decide isn't specially designed to be native — it just ships inside a build that already did
the native-compilation step.**

---

## 3. PBLean: interpreted by default, and the one-flag fix

> **Status (PBLean v0.3.1).** This section describes the problem as it stood through PBLean v0.3.0.
> It is **fixed upstream**: v0.3.1 ships the precompiled `VeriPBReflect` lib described in §5, and
> `lakefile.lean` pins it. The analysis below is kept because it explains *why* the flag matters
> and what it does and does not change about trust.

PBLean checks pseudo-Boolean certificates (RoundingSat + VeriPB) with `checkProofBool`, proved
sound by `checkProof_sound`. Architecturally it is **identical** to bv_decide: untrusted external
solver → verified Lean checker → reflection. The only difference is **packaging**:

- PBLean is a **normal user library**, not part of the toolchain.
- By default, Lake builds what's needed to *import* a library — the `.olean` files carrying the
  *intermediate representation* (IR) the interpreter runs. It **skips** building the library into
  a native `.so` that loads on import, because most library code is never *run* at build time.
- Result: `checkProofBool` has **no native version loaded**, so the **interpreter** walks its IR —
  slowly.

`precompileModules := true` tells Lake to also build that native `.so` and load it. It changes
**no source** and removes **no IR** — it simply **adds** the native form, so the evaluator has
machine code to jump to (exactly like bv_decide's toolchain build). Nothing about PBLean "relies
on the interpreter"; that's just what you get when the native step is skipped.

### Measured effect (LeanCSP's largest instance, a 98 MB certificate)

| How the checker runs | Time to build the theorem |
|---|---|
| Interpreted (PBLean default) | **~21 minutes** |
| Native (with `precompileModules`) | **~70 seconds** (~18× faster) |
| (native checker alone, as a standalone program) | ~49 seconds |

PBLean's *own* test suite shows the same effect: one module dropped from **188 s to 10 s**.

---

## 4. Trust and axioms: what changes, what doesn't

**What "we trust the compiler" means.** Because the theorem comes from *running* the checker
rather than the kernel re-deriving it, you trust that compiling and running the checker yields the
value it is mathematically defined to produce. That means trusting the Lean compiler, all
`@[extern]` / `@[implemented_by]` annotations (functions whose runtime implementation is
hand-written native code — arithmetic, arrays, strings), and the engine that runs it.

**What's still free** (fully kernel-checked, no compiler trust): the soundness theorem
`f cert = true → statement`, and the fact that the external solver is **irrelevant to soundness** —
a wrong certificate just makes the checker return `false`.

**Does going native enlarge the trusted base?**

- **Declared axioms: no change.** Reflection already trusts the compiler either way, so the
  theorem's axiom list is identical.
- **Real trusted base: marginally wider.** Native additionally exercises the C compiler on *this*
  checker's generated code, plus the shared-library loader; interpreted leans on the fixed
  interpreter instead. Same logical status, slightly more moving parts — a refinement *within*
  "trust the compiler," not a jump into it.

### The axiom footprint

Since **Lean 4.29**, the built-in tactics and LeanCSP record the native run differently. Same trust
claim — the difference is bookkeeping granularity.

**`native_decide` and `bv_decide` (4.29+)** mint a **fresh axiom per use**, named after the theorem,
each asserting the one equation that run produced:

```
theorem bv_hard (x y : BitVec 16) : (x &&& y) + (x ||| y) = x + y := by bv_decide
#print axioms bv_hard
-- [propext, Classical.choice, Quot.sound, bv_hard._native.bv_decide.ax_1_5]
```

**LeanCSP** builds the reflection term by hand with `Lean.ofReduceBool` — one blanket axiom
covering every such computation at once:

```
propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler
```

(`Lean.trustCompiler` is a marker axiom meaning "trust the compiler/interpreter and all
`@[extern]`/`@[implemented_by]` code".) This footprint is **identical** whether the checker ran
interpreted or native — precompiling changes only the speed, not the trust statement.

> **Deprecation note (Lean 4.30).** `Lean.ofReduceBool` and `Lean.trustCompiler` are now
> **deprecated** — *"in-kernel native reduction is deprecated; assert native evaluations with
> axioms instead"* (`since := "2026-02-01"`, i.e. the deprecation arrived with 4.30 itself) — and
> are expected to be removed eventually. Nothing breaks today, and no warning fires (the term is
> assembled with `mkConst`, not written as source syntax, and the deprecation linter only sees
> source-level references), but LeanCSP will need to revisit this before removal lands.
>
> **PBLean v0.3.1 has already migrated**, replacing its hand-built `ofReduceBool` term with
> `Lean.Meta.nativeEqTrue` in its own `veripb_reflect`/`schur_reflect` elaborators — a ready-made
> reference for when LeanCSP follows. This does **not** affect LeanCSP today: we never invoke those
> elaborators, we build our own reflection term (`PB/Tactic.lean`, `PB/GenericEncode.lean`) on top
> of `checkProofBool`/`checkProof_sound` (unchanged in v0.3.1), and per-use axioms are minted only
> when the elaborator *runs*, not on import. Verified: LeanCSP's theorems on v0.3.1 still report
> exactly `propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler`.
> Precompilation is orthogonal to this — the `.so` speeds up `ofReduceBool` and `nativeEqTrue`
> alike, so adopting it did not force the migration.

---

## 5. How LeanCSP benefits

LeanCSP certifies UNSAT results (e.g. Schur numbers) by admitting large pseudo-Boolean
certificates through PBLean. The precompile fix matters because:

1. **Large instances become practical.** The Schur `S(4) = 44` upper bound reflects a ~98 MB
   certificate: ~21 minutes interpreted, ~70 seconds native — the difference between "a painful
   one-off" and "a normal part of the build."

2. **Same theorem, same trust.** Identical statement, identical axioms (`Lean.ofReduceBool` /
   `Lean.trustCompiler`). Verified directly with `#print axioms`.

3. **It cost nothing to adopt.** The fix was purely in PBLean's build file: expose the checker's
   closed module set as a small precompiled library, no source changes. It is **upstream as of
   PBLean v0.3.1**, so LeanCSP gets it from the `require veripb ... @ "v0.3.1"` pin in
   `lakefile.lean` — no fork, no divergent copy, no local patching.

4. **It closes the speed gap with bv_decide.** Both then run a verified checker via native
   reflection, at comparable speed. They still differ in proof system (VeriPB vs LRAT) and — since
   Lean 4.29 — in how the native run is recorded (per-use axiom vs `ofReduceBool`, §4).

### The change, concretely

PBLean's `lakefile.toml` gained this lib in **v0.3.1**, everything else untouched:

```toml
# NOTE: must come AFTER the `VeriPB` lib — see below.
[[lean_lib]]
name = "VeriPBReflect"
roots = ["VeriPB.Tactic.Sat.Reflect"]
globs = [
  "VeriPB.Tactic.Sat.PseudoBoolean",
  "VeriPB.Tactic.Sat.FromVeriPB",
  "VeriPB.Tactic.Sat.Reflect",
]
precompileModules = true
```

This publishes the checker's closed module set (`PseudoBoolean → FromVeriPB → Reflect`) as a
precompiled native library.

**Declaration order matters.** Every module belongs to exactly one lib, and when two libs claim
the same module Lake awards it to the one declared **last** (`leanLibs.findSomeRev?` in
`Lake/Config/Module.lean`). Since `precompileModules` only affects modules its own lib owns,
putting this block *before* the wildcard `VeriPB` lib would let `VeriPB` claim all three modules,
leaving `VeriPBReflect` owning nothing and the flag doing **nothing at all** — with no error, so
the build still succeeds and quietly runs interpreted.

*Nothing to do here:* PBLean v0.3.1 already declares the lib last, so LeanCSP (and anyone else
depending on it) gets the native path just by building. This caveat only matters if you apply the
same pattern to a different library.

Downstream projects like LeanCSP load native `checkProofBool` automatically — turning the
21-minute check into a ~70-second one, with no change to the proof or its trust base. Lake
propagates this across packages: it builds `VeriPBReflect:shared` and hands the `.so` to `lean`
when elaborating any module that imports the checker (visible in the `dynlibs` field of that
module's `.lake/build/ir/**/*.setup.json`).
