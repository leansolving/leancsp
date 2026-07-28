import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Proofs.GraphColoringSB
import CSP.L2S.Proofs.SchurSB

/-!
# Parametric CSP generators for the SBC scaling study (v2)

Computable `IntCSP` generators (no proofs) for the *critical* UNSAT instances, scaled by the
hardness parameter.  "Not all equal" over a tuple is expressed with existing encodable patterns:
`schur_triple` (3-ary, any domain) or `at_least_k`/`at_most_k` (binary domain).
-/

open CSP.L2S

namespace Bench

/-- All `k`-combinations of a list (computable). -/
def combinations : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | _, [] => []
  | (k + 1), (x :: xs) => (combinations k xs).map (x :: ·) ++ combinations (k + 1) xs

/-- Edge index of `{i, j}` (i<j) in `Kₙ`, row-major over the strict upper triangle. -/
def edgeIdx (n i j : ℕ) : ℕ := i * n - i * (i + 1) / 2 + (j - i - 1)

-- ============================================================================
-- Van der Waerden:  r colours on {1..n}, no monochromatic k-term AP
-- ============================================================================

/-- All `k`-term APs `(a, a+d, …, a+(k-1)d)` inside `0..n-1`. -/
def vdwAPs (n k : ℕ) : List (List ℕ) :=
  (List.range n).flatMap fun a =>
    (List.range n).filterMap fun d0 =>
      let d := d0 + 1
      if a + (k - 1) * d < n then some ((List.range k).map (fun i => a + i * d)) else none

/-- `r`-colour, `k`-AP Van der Waerden CSP. For 2 colours any `k` uses cardinality;
    for `k = 3` any `r` uses `schur_triple`. -/
def gen_vdw (r k n : ℕ) : IntCSP :=
  let bounds : List (IntConstraint n) :=
    (List.range n).map (fun v => IntConstraint.bound v 0 (r - 1))
  let cons : List (IntConstraint n) :=
    (vdwAPs n k).flatMap fun ap =>
      if k = 3 then
        match ap with
        | [a, b, c] => [IntConstraint.schur_triple a b c]
        | _ => []
      else  -- binary "not all equal" over the AP: 1 ≤ Σ ≤ k-1
        [IntConstraint.at_least_k ap 1, IntConstraint.at_most_k ap (k - 1)]
  ⟨n, bounds ++ cons⟩

/-- 3-term APs of `0..n-1` as `Fin n` triples (all endpoints `< n`). -/
def vdwTriples (n : ℕ) : List (Fin n × Fin n × Fin n) :=
  (vdwAPs n 3).filterMap fun ap =>
    match ap with
    | [a, b, c] =>
      if ha : a < n then
        if hb : b < n then
          if hc : c < n then some (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) else none
        else none
      else none
    | _ => none

/-- Van der Waerden `W(r,3)` CSP built *via* the verified `schur_csp_triples` (bounds `0..r-1` + a
    `schur_triple` per 3-term AP), so `schur_unsat_of_value_precedence` covers its value-precedence
    SBC for *any* number of colours `r` — no new proof. -/
def gen_vdw3 (r n : ℕ) : IntCSP :=
  Schur.schur_csp_triples n r (vdwTriples n)

-- ============================================================================
-- Ramsey:  2-colour edges of Kₙ, no mono K_s in colour 0, no mono K_t in colour 1
-- ============================================================================

/-- Edges (as variable indices) of the clique on vertex set `vs`. -/
def cliqueEdges (n : ℕ) (vs : List ℕ) : List ℕ :=
  (combinations 2 vs).filterMap (fun e => match e with | [i, j] => some (edgeIdx n i j) | _ => none)

/-- Ramsey `R(s,t)` CSP on `Kₙ`: each edge a colour in `{0,1}`; every `s`-clique not all colour 0
    (`at_least_k … 1`) and every `t`-clique not all colour 1 (`at_most_k … |E|-1`). -/
def gen_ramsey (s t n : ℕ) : IntCSP :=
  let m := n * (n - 1) / 2
  let bounds : List (IntConstraint m) :=
    (List.range m).map (fun e => IntConstraint.bound e 0 1)
  let noMono0 : List (IntConstraint m) :=
    (combinations s (List.range n)).map fun vs =>
      IntConstraint.at_least_k (cliqueEdges n vs) 1
  let noMono1 : List (IntConstraint m) :=
    (combinations t (List.range n)).map fun vs =>
      let es := cliqueEdges n vs
      IntConstraint.at_most_k es (es.length - 1)
  ⟨m, bounds ++ noMono0 ++ noMono1⟩

-- ============================================================================
-- Mutilated chessboard:  2k×2k board minus two opposite (same-colour) corners,
-- tiled by dominoes.  REGULAR indexing over every potential domino of the N×N grid
-- (N = 2k): horizontals `h(r,c) = r*(N-1)+c` (c<N-1) in `[0, N(N-1))`, then verticals
-- `v(r,c) = N(N-1) + r*N + c` (r<N-1) in `[N(N-1), 2N(N-1))`.  Dominoes incident to a
-- removed corner are forced to 0 (`bound x 0 0`); present cells get an exactly-one.
-- The diagonal reflection `(r,c)↦(c,r)` is then a CLOSED-FORM arithmetic involution
-- (`h(r,c) ↔ v(c,r)`), enabling a PARAMETRIC variable-symmetry proof (see `MutilatedSB`).
-- UNSAT by colour counting (exponentially hard for resolution, Alekhnovich).
-- ============================================================================

/-- Is `(r,c)` a removed (opposite-corner) cell of the `N×N` board? -/
def mutRemoved (N r c : ℕ) : Bool := (r == 0 && c == 0) || (r == N - 1 && c == N - 1)

/-- Placement `x` is dead (forced to 0) if either of its two cells is a removed corner. -/
def mutDead (k x : ℕ) : Bool :=
  let N := 2 * k
  let nH := N * (N - 1)
  if x < nH then
    mutRemoved N (x / (N - 1)) (x % (N - 1)) || mutRemoved N (x / (N - 1)) (x % (N - 1) + 1)
  else
    mutRemoved N ((x - nH) / N) ((x - nH) % N) || mutRemoved N ((x - nH) / N + 1) ((x - nH) % N)

/-- Indices of the (≤4) potential dominoes incident to cell `(r,c)` of the `N×N` grid. -/
def mutIncident (k r c : ℕ) : List ℕ :=
  let N := 2 * k
  let nH := N * (N - 1)
  (if c + 1 < N then [r * (N - 1) + c] else []) ++          -- right  h(r,c)
  (if 0 < c then [r * (N - 1) + (c - 1)] else []) ++         -- left   h(r,c-1)
  (if r + 1 < N then [nH + r * N + c] else []) ++            -- down   v(r,c)
  (if 0 < r then [nH + (r - 1) * N + c] else [])             -- up     v(r-1,c)

/-- `2k×2k` mutilated-chessboard CSP (regular indexing): a `{0,1}` variable per potential
    domino (corner-incident ones forced to 0) and an exactly-one per present cell. UNSAT. -/
def gen_mutilated (k : ℕ) : IntCSP :=
  let N := 2 * k
  let nplace := 2 * N * (N - 1)
  let bounds := (List.range nplace).map
    (fun x => IntConstraint.bound x 0 (if mutDead k x then 0 else 1))
  let cells := (List.range N).flatMap fun r =>
    (List.range N).filterMap fun c =>
      if mutRemoved N r c then none else some (IntConstraint.exactly_k (mutIncident k r c) 1)
  ⟨nplace, bounds ++ cells⟩

-- ============================================================================
-- Perfect-matching / parity principle:  K_{2m+1} has no perfect matching.
-- One {0,1} var per edge; per-vertex exactly-one over its incident edges.
-- Huge variable symmetry S_{2m+1}; exponentially hard for resolution (Razborov).
-- ============================================================================

/-- Perfect matching on `Kₙ` (`n = 2m+1`) via the n×n adjacency encoding: variable `x_{ij} = i*n+j`
    in `{0,1}` (diagonal forced to 0), symmetric (`x_{ij} = x_{ji}`), each row summing to 1.  The
    vertex transposition `(0 1)` is then a closed-form index involution (`matchSwap`), enabling a
    PARAMETRIC variable-symmetry proof (see `MatchingSB`).  Odd `n` ⇒ no perfect matching ⇒ UNSAT
    (the parity principle, exponentially hard for resolution). -/
def gen_matching (m : ℕ) : IntCSP :=
  let n := 2 * m + 1
  let bounds := (List.range (n * n)).map
    (fun x => IntConstraint.bound x 0 (if x / n == x % n then 0 else 1))
  let symm := (List.range n).flatMap fun i => (List.range n).filterMap fun j =>
    if i < j then some (IntConstraint.eq (i * n + j) (j * n + i)) else none
  let rows := (List.range n).map fun i =>
    IntConstraint.exactly_k ((List.range n).map (fun j => i * n + j)) 1
  ⟨n * n, bounds ++ symm ++ rows⟩

/-- Vertex transposition `(0 1)` on the n×n adjacency indices: a closed-form involution. -/
def matchSwap (m x : ℕ) : ℕ :=
  let n := 2 * m + 1
  (if x / n = 0 then 1 else if x / n = 1 then 0 else x / n) * n +
    (if x % n = 0 then 1 else if x % n = 1 then 0 else x % n)

/-- Variable SBC for the matching: order the two edges the vertex swap `(0 1)` exchanges
    (`x_{0,2}` vs `x_{1,2}`), breaking the transposition symmetry (non-trivial for `m ≥ 1`). -/
def matching_sbc (m : ℕ) : IntConstraint ((2 * m + 1) * (2 * m + 1)) :=
  IntConstraint.le 2 (matchSwap m 2)

-- ============================================================================
-- Variable symmetry-breaking constraints for the geometric families.
-- ============================================================================

/-- The diagonal reflection `(r,c)↦(c,r)` on placement indices: a closed-form involution
    swapping horizontal `h(r,c)` with vertical `v(c,r)` (`N = 2k`, `nH = N(N-1)`). -/
def mutRefl (k x : ℕ) : ℕ :=
  let N := 2 * k
  let nH := N * (N - 1)
  if x < nH then nH + (x % (N - 1)) * N + (x / (N - 1))        -- h(r,c) ↦ v(c,r)
  else ((x - nH) % N) * (N - 1) + ((x - nH) / N)               -- v(r,c) ↦ h(c,r)

/-- Variable SBC for the mutilated board: order placement 1 against its diagonal-reflection
    image, breaking the order-2 board reflection symmetry (non-trivial for `k ≥ 2`). -/
def mutilated_sbc (k : ℕ) : IntConstraint (2 * (2 * k) * (2 * k - 1)) :=
  IntConstraint.le 1 (mutRefl k 1)

-- ============================================================================
-- Langford L(2,n):  place 1,1,2,2,…,n,n so the two copies of d are d+1 apart.
-- Mirrors `Tests/lean/10_langford_simple.lean langford_2n_csp`.  UNSAT iff
-- n ≡ 1,2 (mod 4).  Reversal (order-2) variable symmetry; SBC = `x₀ ≥ n` (see `langford_sbc`).
-- ============================================================================

/-- `L(2,n)` CSP: `2n` position variables (domain `1..2n`), `alldifferent`, and a
    spacing equation `x[2d+1] − x[2d] = d+2` per digit. -/
def gen_langford (n : ℕ) : IntCSP :=
  let nv := n * 2
  let bounds : List (IntConstraint nv) :=
    (List.range nv).map (fun i => IntConstraint.bound i 1 (nv : ℤ))
  let spacing : List (IntConstraint nv) := (List.range n).filterMap fun (d0 : ℕ) =>
    let v1 : ℕ := d0 * 2
    let v2 : ℕ := d0 * 2 + 1
    if h1 : v1 < nv then
      if h2 : v2 < nv then
        some (linear_eq (⟨#[⟨v2, h2⟩, ⟨v1, h1⟩], rfl⟩ : _root_.Vector (VarType nv) 2)
                        (⟨#[1, -1], rfl⟩ : _root_.Vector ℤ 2) ((d0 : ℤ) + 2))
      else none
    else none
  let alldiff : IntConstraint nv := alldifferent (_root_.Vector.ofFn id)
  ⟨nv, bounds ++ spacing ++ [alldiff]⟩

/-- Variable SBC for Langford: digit-0's first copy lies in the **second** half (`x₀ ≥ n`), the
    upper-half representative of the sequence reversal `p ↦ 2n+1-p`.  Sound for all `n` (non-trivial
    for `n ≥ 1`); verified in `Proofs/LangfordSB.lean`.  The equivalent lower-half form `x₀ ≤ n-1`
    (its mirror image under the reversal) is kept as `langford_sbc'`. -/
def langford_sbc (n : ℕ) : IntConstraint (n * 2) :=
  IntConstraint.ge_const 0 (n : ℤ)

/-- Lower-half variant of `langford_sbc`: digit-0's first copy lies in the first half (`x₀ ≤ n-1`).
    The mirror image of `langford_sbc` under the reversal `p ↦ 2n+1-p`; equally sound (verified in
    `Proofs/LangfordSB.lean`). -/
def langford_sbc' (n : ℕ) : IntConstraint (n * 2) :=
  IntConstraint.le_const 0 ((n : ℤ) - 1)

-- ============================================================================
-- Clique-colouring / chromatic family:  Mycielskian graphs Mⱼ are triangle-free
-- yet χ(Mⱼ) = j+2, so colouring with χ−1 = j+1 colours is UNSAT.  Unlike Kₙ the
-- chromatic number exceeds the clique number — the genuine clique-colouring
-- spirit — and for j ≥ 2 there are ≥3 interchangeable colours, so value
-- precedence is non-trivial here.  M₂ = Grötzsch graph (11 vtx, χ4).
-- ============================================================================

/-- One Mycielski step: doubles the vertex set (shadows) and adds an apex; raises
    the chromatic number by 1.  Vertices `0..v-1` originals, `v..2v-1` shadows,
    `2v` apex. -/
def mycielskiStep : ℕ × List (ℕ × ℕ) → ℕ × List (ℕ × ℕ)
  | (v, es) =>
    let shadow := es.flatMap (fun e => [(v + e.1, e.2), (e.1, v + e.2)])
    let apex := (List.range v).map (fun i => (2 * v, v + i))
    (2 * v + 1, es ++ shadow ++ apex)

/-- `Mⱼ` as `(numVertices, edges)`; `M₀ = K₂` (χ2), each step +1 chromatic, so
    `χ(Mⱼ) = j + 2`. -/
def mycielskiGraph : ℕ → ℕ × List (ℕ × ℕ)
  | 0 => (2, [(0, 1)])
  | (j + 1) => mycielskiStep (mycielskiGraph j)

/-- Mycielskian edges as `Fin`-typed pairs (all endpoints are `< numVertices`). -/
def mycielskiFinEdges (j : ℕ) : List (Fin (mycielskiGraph j).1 × Fin (mycielskiGraph j).1) :=
  (mycielskiGraph j).2.filterMap fun e =>
    if h1 : e.1 < (mycielskiGraph j).1 then
      if h2 : e.2 < (mycielskiGraph j).1 then some (⟨e.1, h1⟩, ⟨e.2, h2⟩) else none
    else none

/-- Colour `Mⱼ` (χ = j+2) with only `j+1` colours — UNSAT.  Built *via* the verified
    `graph_coloring_csp`, so `graph_coloring_unsat_of_value_precedence` covers its value-precedence
    SBC directly (no new proof needed). -/
def gen_clique_coloring (j : ℕ) : IntCSP :=
  graph_coloring_csp (mycielskiGraph j).1 (mycielskiFinEdges j) (j + 1)

end Bench
