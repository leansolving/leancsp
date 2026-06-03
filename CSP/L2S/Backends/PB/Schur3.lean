import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«11_schur»

namespace CSP.L2S.PB.Schur3

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the 3-colour Schur corpus CSP `schur_3_14`

`schur_3_14` (`Tests/lean/11_schur.lean`) is the CSP form of the Schur bound
**S(3) = 13**: `{1,…,14}` cannot be partitioned into three sum-free sets.  Each
ball `1..14` gets a colour variable over `{1,2,3}`; for every sum triple
`x + y = z` (`x ≤ y`, `z ≤ 14`, including the diagonals `i+i=2i`) the three
colours are **not all equal** — a `schur_triple` constraint.

This is the first end-to-end use of the **multi-valued** not-all-equal encoder
(`encodeNotAllEqualMulti`, `AllDifferent.lean`): the binary bottom-threshold
reduction used for `schur_2_5` / `vdw_2_3_9` / `ramsey_3_3_K6` does not apply once
the colour domain has `k > 2` values.  Not-all-equal is encoded as the per-value
cardinality decomposition `∀ val ∈ {1,2,3} : Σⱼ ⟦xⱼ = val⟧ ≤ 2`, which is
aux-free, so it rides on the generic spine `csp_unsat_generic` through the bridges
`schur_triple_sat` / `extend_sat_encodeNotAllEqualMulti` (`NotAllEqualBridge.lean`)
exactly as the binary cases do.

The colour domain `{1,2,3}` has width 2, so each ball has two threshold bits and
the order-encoding `monotonicity` is **non-empty** (one staircase clause per ball,
unlike the binary instances).  Ball `i` maps to OPB thresholds `x{2i+1}, x{2i+2}`.
-/

/-! ### The signature, the resolved triple list, and corpus membership -/

/-- The PB signature for `schur_3_14`: fourteen integer (colour) variables, each
    over the three-element domain `{1,2,3}`, no Boolean or auxiliary variables. -/
def schur3Sig : CSPSig where
  nInt := 14
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 3
  sorted := fun _ => domainValues_sorted 1 3
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Every colour variable has the three-element domain, width `2 > 0`. -/
theorem schur3Sig_width (i : Fin schur3Sig.nInt) : 0 < schur3Sig.width i := by
  show 0 < (domainValues 1 3).length - 1; decide

/-- The corpus sum triples resolved to in-range `Fin 14` variable indices. -/
def schur3T : List (Fin 14 × Fin 14 × Fin 14) :=
  (generate_schur_triples 14).filterMap (fun p =>
    if h1 : p.1 < 14 then if h2 : p.2.1 < 14 then if h3 : p.2.2 < 14 then
      some (⟨p.1, h1⟩, ⟨p.2.1, h2⟩, ⟨p.2.2, h3⟩) else none else none else none)

/-- Each resolved sum triple's `schur_triple` constraint is in
    `schur_3_14.constraints` (one of the `make_schur_constraints`). -/
theorem schur3T_mem_constraints (t : Fin 14 × Fin 14 × Fin 14) (ht : t ∈ schur3T) :
    schur_triple t.1 t.2.1 t.2.2 ∈ schur_3_14.constraints := by
  rw [schur3T, List.mem_filterMap] at ht
  obtain ⟨p, hp_mem, hp_eq⟩ := ht
  obtain ⟨i, j, k⟩ := p
  simp only at hp_eq
  split_ifs at hp_eq with h1 h2 h3
  rw [Option.some.injEq] at hp_eq
  subst hp_eq
  show schur_triple (⟨i, h1⟩ : Fin 14) ⟨j, h2⟩ ⟨k, h3⟩ ∈
    schur_bounds 14 3 ++ make_schur_constraints 14 (generate_schur_triples 14)
  apply List.mem_append_right
  rw [make_schur_constraints, List.mem_filterMap]
  exact ⟨(i, j, k), hp_mem, by simp only [dif_pos h1, dif_pos h2, dif_pos h3]⟩

/-! ### The PB encoding and certificate -/

/-- The PB user constraints: the normalized multi-valued not-all-equal encoding of
    each sum triple over the colour domain `{1,2,3}` (the order-encoding staircase
    clauses are added by the spine). -/
def schur3User : List (PBConstr (PBVar schur3Sig)) :=
  schur3T.flatMap (fun t =>
    (encodeNotAllEqualMulti [t.1, t.2.1, t.2.2] [1, 2, 3]).filterMap normalize)

/-- The veripb-elaborated kernel proof of UNSAT for `schur3User`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The 14 colours give 28 threshold
    variables (ball `i` ↦ OPB `x{2i+1}, x{2i+2}`); the 14 monotonicity clauses and
    147 per-value not-all-equal clauses (49 sum triples × 3 colours) form the OPB. -/
def schur3KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 161;
rup >= 0 : ~ ;
pol 15 s;
pol 16 s;
pol 17 s;
pol 54 s;
pol 55 s;
pol 56 s;
pol 87 s;
pol 88 s;
pol 89 s;
pol 114 s;
pol 115 s;
pol 116 s;
pol 135 s;
pol 136 s;
pol 137 s;
pol 150 s;
pol 151 s;
pol 152 s;
pol 159 s;
pol 160 s;
pol 161 s;
pol 120 67 + 73 + s 177 + 95 + s;
pol 117 70 + 64 + s;
pol 82 153 + 123 + s 185 + s 101 + 41 + s 110 + s 44 + s;
pol 76 138 + 117 + s 107 + 47 + s 176 + 79 + s 186 + s 178 + s 120 + s;
pol 117 76 + 139 + s 123 + s 185 + s 35 + 104 + s 38 + s 67 + s 187 + s 184 + s 172 + s 167 + s 171 + s 23 + s;
pol 82 144 + 50 + 73 + s 79 + s;
pol 93 157 + 112 + s 122 + 134 + s;
pol 32 100 + 170 + s 105 + 141 + s 189 + s 190 + s;
pol 134 189 + 112 + s 178 + 169 + s 191 + s 174 + s 167 + s 175 + s 117 + s 147 + s;
pol 90 167 + 142 + 180 + 122 + s 32 + s 139 + s 105 + s 169 + s 58 + s 177 + s;
pol 132 85 + 79 + s;
pol 29 58 + 170 + s;
pol 99 176 + 142 + s 180 + 29 + s 32 + s;
pol 129 82 + 167 + s 50 + 26 + s 179 + 139 + s 196 + s 105 + s 195 + s;
pol 146 82 + 103 + s 129 + 172 + s 167 + s 26 + s 58 + s 169 + 197 + s 193 + s 192 + s 76 + s;
pol 79 120 + 178 + s;
pol 70 35 + 105 + 90 + s 67 + s 179 + s 195 + s 199 + s 172 + s 167 + s 26 + s 29 + s 5 + s;
pol 183 148 + 64 + s 132 + 105 + 90 + s 176 + s 58 + s;
pol 35 73 + 185 + s 175 + 141 + s 201 + s;
pol 196 58 + s 175 + 179 + s 79 + s;
pol 125 64 + 167 + s 99 + 201 + s 176 + s 58 + s;
pol 35 70 + 73 + s 105 + 93 + s;
pol 32 100 + 170 + s 205 + s 175 + s 141 + s 204 + s 203 + s;
pol 175 79 + 58 + s 178 + 169 + s 206 + s 200 + s 44 + s 47 + s;
pol 167 122 + 117 + 79 + s 106 + s;
pol 167 122 + 185 + s 100 + s 141 + 208 + s 180 + s 32 + s 170 + s;
pol 157 32 + 183 + s 35 + s;
pol 70 105 + 141 + s;
pol 134 167 + 182 + 185 + s;
pol 157 134 + 122 + s 174 + s 167 + 123 + 212 + s;
pol 185 90 + s 167 + s 174 + 73 + s 213 + s 210 + s 93 + s 111 + s 209 + s 175 + s 138 + s 5 + s;
pol 109 120 + 169 + s 154 + s 50 + 129 + s 200 + s 29 + s 70 + s 185 + s;
pol 120 73 + 67 + s 32 + 35 + s 215 + s 172 + s;
pol 67 102 + 169 + s 32 + 58 + s 64 + s 174 + 26 + s 167 + s 216 + s;
pol 99 176 + 58 + s 26 + 167 + s 123 + s 217 + s;
pol 213 210 + s 102 + s 111 + s 169 + s 58 + s 177 + s 218 + s 214 + s 198 + s 207 + s;
pol 93 73 + 176 + s;
pol 64 99 + 175 + s 220 + s;
pol 172 167 + 67 + s 26 + 29 + s;
pol 125 139 + 167 + 102 + 172 + s 67 + s 32 + s 175 + 221 + s 220 + s 222 + s 169 + s;
pol 131 109 + 167 + 144 + 172 + s 73 + s 175 + s;
pol 73 120 + 172 + s 167 + s 26 + 195 + s 58 + s 224 + s 223 + s 38 + s 41 + s 219 + s 188 + s;
pol 153 109 + 91 + s 35 + 146 + s 95 + s 173 + s 66 + s 121 + s 177 + s 26 + s 29 + s;
pol 138 124 + 121 + s 104 + 171 + s 91 + s 35 + s;
pol 91 171 + 32 + s 121 + s 66 + 173 + s 227 + s;
pol 103 138 + 66 + s 170 + s 125 + 32 + s 100 + s 174 + s 23 + s 228 + s 63 + s 176 + s;
pol 138 94 + 103 + s 101 + 35 + s;
pol 103 174 + 23 + s 124 + s 138 + 63 + s;
pol 23 94 + 173 + s;
pol 124 69 + 75 + s 118 + s 174 + 232 + s 231 + s 230 + s 66 + s;
pol 124 69 + 75 + s;
pol 154 81 + 110 + 171 + s 124 + s 91 + s 63 + s 118 + s 234 + s;
pol 170 32 + 101 + s;
pol 170 122 + 23 + s 235 + s 236 + s 233 + s 41 + s 44 + s 229 + s 226 + s;
pol 157 111 + 102 + s 139 + s 122 + 134 + s 44 + s 176 + s 174 + s 26 + s;
pol 118 234 + s 177 + 41 + s 44 + s;
pol 29 121 + 176 + s;
pol 139 75 + 32 + 118 + s 239 + s 177 + s 41 + s 44 + s 240 + s 238 + s 169 + s 57 + s 237 + s;
pol 47 142 + 234 + s 69 + s 118 + s;
pol 154 99 + 108 + s 170 + s;
pol 130 153 + 69 + s 91 + s 169 + s 243 + s 95 + 146 + s 29 + s 242 + s 35 + s 38 + s 173 + s;
pol 50 145 + 179 + 196 + s 108 + s 169 + s 94 + s 174 + 23 + s 26 + s 244 + s 72 + s 175 + s 78 + s 10 + s 241 + s 166 + s 225 + s 165 + s;
pol 125 139 + 64 + s 102 + 33 + s 67 + s 163 + s 28 + 245 + s;
pol 67 57 + 93 + s 246 + s;
pol 31 245 + 63 + 163 + s;
pol 131 154 + 70 + s 144 + 33 + s 36 + s 67 + s 164 + 245 + s 248 + s;
pol 33 64 + 67 + s 163 + s 28 + 245 + s 249 + s 92 + s 170 + s 247 + s;
pol 131 145 + 37 + 245 + s 66 + 69 + s 164 + 245 + s 153 + s 30 + s;
pol 92 94 + 34 + 245 + s 66 + 163 + s;
pol 92 58 + 64 + s 252 + s 251 + s;
pol 103 92 + 125 + s 34 + 245 + s 63 + 66 + s 164 + 245 + s 138 + s 27 + s 253 + s 169 + s;
pol 81 109 + 43 + 245 + s 57 + s 163 + s;
pol 144 109 + 73 + s 220 + s 255 + s 175 + s;
pol 82 108 + 42 + s 58 + s 164 + 245 + s;
pol 108 145 + 94 + s 72 + s 257 + s 176 + s 256 + s 155 + 125 + s;
pol 34 245 + 72 + 99 + s 176 + 57 + s;
pol 72 94 + 176 + s;
pol 100 63 + 175 + s 260 + s 259 + s 163 + s;
pol 33 73 + 100 + s 175 + 58 + s 164 + 245 + s 221 + s 261 + s 258 + s 122 + s 171 + s 250 + s 254 + s;
pol 45 106 + 76 + s 143 + 92 + s 125 + s 70 + s 33 + s 36 + s;
pol 30 70 + 67 + s 125 + 140 + s 76 + s 42 + s 39 + s 73 + s 263 + s 164 + 245 + s;
pol 103 92 + 125 + s 34 + 245 + s 69 + 75 + s 37 + 245 + s;
pol 31 245 + 125 + 140 + s 43 + 245 + s 69 + 75 + s 40 + 245 + s 72 + s 66 + s 265 + s 163 + s 264 + s;
pol 31 245 + 125 + 140 + s;
pol 43 245 + 72 + 102 + s;
pol 46 245 + 143 + 105 + 75 + s 34 + 245 + s 37 + 245 + s 268 + s 267 + s;
pol 40 245 + 69 + 99 + s 269 + s 163 + s;
pol 73 99 + 33 + s;
pol 76 140 + 42 + 39 + s 67 + s 73 + s;
pol 125 76 + 70 + s 102 + 36 + s 272 + s 271 + s 164 + 245 + s 270 + s 169 + s 266 + s 177 + s 119 + s 262 + s 168 + s 174 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 36 118 + 273 + 25 + 274 + s 65 + 71 + s;
pol 121 273 + 108 + 140 + 177 + s 130 + 273 + s 118 + 273 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 140 31 + 245 + 25 + 277 + s 36 + 276 + s 77 + s 83 + s 124 + 273 + s 275 + s 102 + s 169 + s 93 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 113 182 + 124 + 273 + s 156 + 138 + s 31 + 245 + s 25 + 279 + s;
pol 51 182 + 130 + 273 + 113 + 77 + s 83 + s;
pol 80 176 + 142 + s;
pol 80 179 + 121 + 273 + s 138 + 282 + s 42 + s 45 + s 124 + 273 + s 281 + s 36 + s 280 + s 171 + s 59 + s 91 + 273 + s;
pol 101 121 + 273 + 170 + s 155 + s 130 + 273 + s 27 + 36 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 156 133 + 273 + 121 + 273 + s 101 + 171 + s 22 + 285 + s 284 + s 144 + s 175 + s 275 + s 183 + s 71 + s 283 + s 278 + s;
deld 274 277 279 285;
pol 113 43 + 245 + 133 + 273 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 49 245 + 110 + 80 + s 287 + s 138 + 175 + s 25 + 288 + s 59 + s 22 + 289 + s 153 + s 169 + s 178 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 77 103 + 106 + s 123 + 117 + s 172 + s 22 + 291 + s 171 + 179 + s 80 + s 74 + s 164 + 245 + s 63 + s 141 + s;
pol 74 34 + 245 + 164 + 245 + s 172 + 166 + s 91 + 273 + s 171 + 31 + 245 + s 292 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 104 124 + 273 + 22 + 294 + s 166 + 164 + 245 + s 74 + s 34 + 245 + s;
pol 83 49 + 245 + 46 + 245 + s 80 + s 164 + 245 + s 153 + 63 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 22 297 + 280 + s 172 + s 295 + s 296 + s 138 + s 178 + s 6 + s 293 + s;
rup 1 x2 1 x8 >= 2 : 245 273 ~;
pol 153 145 + 28 + 245 + s 110 + 171 + s 94 + s 34 + 245 + s 74 + s 164 + 245 + s 172 + 166 + s 25 + 299 + s 298 + s;
rup 1 x2 1 x8 >= 2 : 245 273 ~;
pol 74 164 + 245 + 173 + 273 + 57 + 93 + s 25 + 301 + s;
pol 74 34 + 245 + 164 + 245 + s 90 + 172 + s 166 + s 302 + s 300 + s;
pol 28 245 + 169 + 155 + 94 + s 145 + s 117 + 129 + s 37 + 245 + s 173 + 273 + s 71 + s 74 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 302 22 + 305 + s;
pol 304 164 + 245 + s 172 + 166 + s 306 + s 101 + s 303 + s 177 + s;
pol 68 34 + 245 + 31 + 245 + s;
pol 145 117 + 129 + s 37 + 245 + s 155 + 68 + s;
pol 40 245 + 117 + 175 + s 28 + 245 + s 309 + s 71 + s 65 + s 308 + s 164 + 245 + s 90 + s 166 + s;
pol 65 31 + 245 + 28 + 245 + s 99 + 175 + s 121 + 273 + s 68 + s;
pol 78 179 + 121 + 273 + s;
pol 49 245 + 78 + 108 + s;
pol 111 133 + 273 + 43 + 245 + s 313 + s 140 + 312 + s 143 + s 183 + s;
pol 111 133 + 273 + 43 + 245 + s 313 + s 158 + 180 + s 140 + s;
rup 1 x2 1 x8 >= 2 : 245 273 ~;
pol 243 121 + 273 + s 315 + s 314 + s 146 + s 25 + 316 + s 57 + s 164 + 245 + s 311 + s 173 + 273 + s 310 + s 169 + s 3 + s;
rup 1 x2 1 x8 >= 2 : 245 273 ~;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 138 121 + 273 + 43 + 245 + s 175 + s 25 + 318 + s 95 + 104 + s 22 + 319 + s 173 + 273 + s;
pol 31 245 + 123 + 138 + s 43 + 245 + s 71 + 77 + s 40 + 245 + s 117 + s 176 + s;
pol 28 245 + 120 + 175 + s 321 + s;
pol 83 109 + 43 + 245 + s 153 + 123 + s 100 + s 120 + s 170 + s 59 + s 65 + s 322 + s 164 + 245 + s 166 + s 320 + s;
pol 123 43 + 245 + 100 + s 140 + 65 + s;
pol 123 100 + 43 + 245 + s 71 + 77 + s 40 + 245 + s 117 + s 94 + s 324 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 123 103 + 34 + 245 + s 140 + 65 + s 94 + s 175 + 325 + s 68 + s 164 + 245 + s 166 + s 22 + 326 + s 171 + s 323 + s 317 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 22 328 + 99 + 59 + 286 + s 164 + 245 + s 72 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 140 43 + 245 + 121 + 273 + s 102 + 290 + s 22 + 330 + s 181 + s 59 + s 286 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
pol 268 22 + 332 + s 140 + 171 + s 121 + 273 + s 66 + s 164 + 245 + s 331 + s 329 + s;
rup 1 x2 1 x8 >= 2 : 273 245 ~;
rup 1 x2 1 x8 >= 2 : 245 273 ~;
pol 287 156 + 138 + s 121 + 273 + s 171 + s 22 + 334 + s 93 + s 175 + s 25 + 335 + s 333 + s 172 + s 327 + s 307 + s;
rup 1 ~x3 >= 1 : ~ 336 163;
pol 101 282 + 176 + s 30 + 336 + 27 + 336 + s 178 + s;
pol 286 33 + 336 + s;
rup 1 ~x3 1 x8 >= 2 : 337 273 ~;
pol 27 336 + 121 + 273 + 176 + s 74 + 173 + 273 + s 339 + s 167 + 340 + s;
pol 48 336 + 145 + 179 + 110 + 338 + s 94 + s 80 + s 74 + s;
pol 104 67 + 337 + 139 + s 30 + 336 + 123 + s 64 + 337 + s 101 + s 58 + 337 + s 342 + s 176 + s 172 + s 21 + 336 + s 24 + 336 + s 341 + s;
pol 184 337 + 59 + s 170 + s 172 + s 21 + 336 + s 121 + 273 + s;
rup 1 ~x3 1 x8 >= 2 : 337 273 ~;
pol 184 337 + 100 + 172 + s 143 + s 167 + 345 + s 79 + 337 + s;
pol 100 65 + 59 + s 346 + s 30 + 336 + 169 + s 178 + s 344 + s 177 + s 343 + s;
pol 123 103 + 173 + 273 + s 33 + 336 + s 100 + s;
pol 339 173 + 273 + s;
pol 348 65 + 140 + s 177 + s 94 + s 172 + 21 + 336 + s 24 + 336 + s 349 + s 68 + s;
rup 1 ~x3 1 x8 >= 2 : 337 273 ~;
pol 109 146 + 48 + 336 + 73 + 337 + s 79 + 337 + s 177 + s 58 + 337 + s 172 + 21 + 336 + s 24 + 336 + s 167 + 351 + s 350 + s 171 + s 180 + s 347 + s;
rup 1 x20 >= 1 : ~ 352 10;
rup 1 ~x17 >= 1 : ~ 352 336 39;
rup 1 ~x9 >= 1 : ~ 352 175;
rup 1 ~x21 >= 1 : ~ 352 336 42;
pol 158 112 + 356 + 103 + 356 + s;
rup 1 ~x3 1 ~x9 >= 2 : 337 355 ~;
pol 68 58 + 358 + 94 + 355 + s 140 + s 357 + s 170 + s;
rup 1 ~x9 1 ~x17 >= 2 : 354 355 ~;
rup 1 ~x9 1 ~x21 >= 2 : 356 355 ~;
pol 148 360 + 77 + 113 + s 139 + 361 + s 59 + s;
rup 1 ~x9 1 ~x21 >= 2 : 356 355 ~;
pol 139 363 + 104 + 184 + 337 + s 67 + 337 + s 362 + s 171 + s 359 + s 120 + 352 + s 132 + 352 + s 172 + s 21 + 336 + s;
rup 1 ~x4 >= 1 : ~ 364 337 273 167;
rup 1 ~x15 >= 1 : ~ 364 365 339;
rup 1 ~x16 >= 1 : ~ 365 364 349;
rup 1 x12 >= 1 : ~ 367 365 68;
rup 1 x8 1 ~x7 1 ~x21 >= 3 : 356 364 273 ~;
rup 1 ~x9 1 x12 1 ~x21 >= 3 : 356 355 368 ~;
rup 1 x8 1 ~x7 1 ~x9 1 ~x17 >= 4 : 364 354 355 273 ~;
pol 124 369 + 30 + 336 + 71 + 365 + 139 + 370 + s 118 + 371 + s 104 + 367 + 59 + 365 + s;
rup 1 x8 1 ~x7 1 ~x21 >= 3 : 356 364 273 ~;
rup 1 ~x9 1 x12 1 ~x21 >= 3 : 356 355 368 ~;
rup 1 x8 1 ~x7 1 ~x9 1 ~x17 >= 4 : 364 354 355 273 ~;
pol 30 336 + 124 + 373 + 139 + 374 + s 71 + 365 + 77 + 365 + s 118 + 375 + s;
rup 1 x26 >= 1 : ~ 376 367 146;
rup 1 x14 >= 1 : ~ 376 365 65;
rup 1 x11 >= 1 : ~ 377 352 378 368 372 243;
rup 1 ~x23 >= 1 : ~ 379 178;
rup 1 ~x5 >= 1 : ~ 379 169;
rup 1 ~x13 >= 1 : ~ 379 336 30;
rup 1 x6 1 ~x5 1 x8 1 ~x7 1 x14 1 ~x13 >= 6 : 382 381 372 378 364 273 ~;
pol 91 383 +;
output NONE ;
conclusion UNSAT : 384;
end pseudo-Boolean proof;
"

/-- The PB encoding of `schur_3_14` is unsatisfiable — established by the external
    PB certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted).  The 28 colour thresholds map to OPB `x1,…,x28`. -/
theorem schur3_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((schur3Sig.monotonicity ++ schur3User).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 28 schur3KernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain 3-colouring under which every sum
    triple is not monochromatic. -/
theorem schur3_no_sol : ¬ ∃ (a : Fin schur3Sig.nInt → Int) (_ : Fin schur3Sig.nBool → Bool),
    (∀ i, a i ∈ schur3Sig.values i) ∧
    (∀ t ∈ schur3T, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2) := by
  apply csp_unsat_generic schur3Sig schur3User
    (fun a _ => ∀ t ∈ schur3T, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2)
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    simp only [schur3User, List.mem_flatMap] at hc
    obtain ⟨t, ht, hc⟩ := hc
    refine extend_sat_encodeNotAllEqualMulti a bA _ hdom [t.1, t.2.1, t.2.2] [1, 2, 3] ?_ c hc
    rcases hP t ht with h | h | h
    · exact ⟨t.1, by simp, t.2.1, by simp, h⟩
    · exact ⟨t.1, by simp, t.2.2, by simp, h⟩
    · exact ⟨t.2.1, by simp, t.2.2, by simp, h⟩
  · exact schur3_formulaUnsat

/-- **End-to-end 3-colour Schur UNSAT.** The corpus CSP `schur_3_14` — the
    S(3) = 13 instance, "`{1,…,14}` cannot be 3-coloured sum-free" — is
    unsatisfiable, discharged through the verified PB pipeline: the `schur_triple`
    bridge turns any solution into not-all-equal facts on each sum triple, the
    **multi-valued** not-all-equal encoder turns those into per-value cardinality
    PB constraints (`Σⱼ ⟦xⱼ = v⟧ ≤ 2`), the generic spine `csp_unsat_generic`
    builds the PB model, and the committed certificate `schur3_formulaUnsat`
    contradicts it. -/
theorem schur_3_14_unsat : ¬ schur_3_14.isSatisfiable := by
  rintro ⟨a, hsol⟩
  -- Every colour lies in `{1,2,3}` (from its `bound`).
  have hdom : ∀ i : Fin schur3Sig.nInt, a i ∈ schur3Sig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (3 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (3 : ℕ) a hb
    have h2' : a i ≤ 3 := by exact_mod_cast h2
    show a i ∈ domainValues 1 3
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- Every sum triple is not monochromatic (from its `schur_triple`).
  have hP : ∀ t ∈ schur3T, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2 := by
    intro t ht
    exact schur_triple_sat t.1 t.2.1 t.2.2 a (hsol _ (schur3T_mem_constraints t ht))
  exact schur3_no_sol ⟨a, fun _ => false, hdom, hP⟩

end CSP.L2S.PB.Schur3
