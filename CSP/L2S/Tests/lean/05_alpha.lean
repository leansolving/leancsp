import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Alphabet Music Puzzle

A cryptarithmetic puzzle where letters a-z are assigned numbers 1-26
such that musical words sum to specific target values.

## Problem Description
- 26 variables (a through z), each assigned a unique number from 1 to 26
- 20 equations like "ballet = b+a+l+l+e+t = 45"
- All letters must have different values

## General Pattern
This generalizes to any alphametic/word puzzle where:
- Letters are mapped to a range of numbers
- Words (letter combinations) must sum to target values
- All letters have distinct values
-/

-- Helper to create uniform bounds for all letters
def letter_bounds (n_letters : ℕ) (lb ub : ℤ) : List (TaggedConstraint n_letters) :=
  (List.finRange n_letters).map fun i => bound i lb ub

-- Helper to convert list of nat indices to vector of Fin, with explicit proofs
def make_fin_vector (n : ℕ) (indices : List ℕ) :
    (h : ∀ i ∈ indices, i < n) → _root_.Vector (Fin n) indices.length :=
  fun h =>
    ⟨(indices.attach.map fun ⟨i, hi⟩ => ⟨i, h i hi⟩).toArray, by simp [List.length_attach]⟩

-- General word puzzle CSP - parametrized
def word_puzzle_csp (n_letters : ℕ) (lb ub : ℤ) (word_sums : List (List ℕ × ℤ))
    (h : ∀ pair ∈ word_sums, ∀ i ∈ pair.1, i < n_letters) : HomogeneousCSP :=
  let bounds_list := letter_bounds n_letters lb ub
  let alldiff := alldifferent (_root_.Vector.ofFn id)
  let sum_constraints := word_sums.attach.map fun ⟨(letters, target), hw⟩ =>
    sum_eq (make_fin_vector n_letters letters (h (letters, target) hw)) target
  ⟨n_letters, bounds_list ++ [alldiff] ++ sum_constraints⟩

-- Specific instance: Alpha puzzle with musical words
def alpha_puzzle : HomogeneousCSP :=
  let n := 26
  -- Letter mapping: a=0, b=1, c=2, d=3, e=4, f=5, g=6, h=7, i=8, j=9,
  --                k=10, l=11, m=12, n=13, o=14, p=15, q=16, r=17,
  --                s=18, t=19, u=20, v=21, w=22, x=23, y=24, z=25
  let word_sums : List (List ℕ × ℤ) := [
    ([1,0,11,11,4,19], 45),            -- ballet
    ([2,4,11,11,14], 43),              -- cello
    ([2,14,13,2,4,17,19], 74),         -- concert
    ([5,11,20,19,4], 30),              -- flute
    ([5,20,6,20,4], 50),               -- fugue
    ([6,11,4,4], 66),                  -- glee
    ([9,0,25,25], 58),                 -- jazz
    ([11,24,17,4], 47),                -- lyre
    ([14,1,14,4], 53),                 -- oboe
    ([14,15,4,17,0], 65),              -- opera
    ([15,14,11,10,0], 59),             -- polka
    ([16,20,0,17,19,4,19], 50),        -- quartet
    ([18,0,23,14,15,7,14,13,4], 134),  -- saxophone
    ([18,2,0,11,4], 51),               -- scale
    ([18,14,11,14], 37),               -- solo
    ([18,14,13,6], 61),                -- song
    ([18,14,15,17,0,13,14], 82),       -- soprano
    ([19,7,4,12,4], 72),               -- theme
    ([21,8,14,11,8,13], 100),          -- violin
    ([22,0,11,19,25], 34)              -- waltz
  ]
  word_puzzle_csp n 1 26 word_sums (by
    intro pair hp i hi
    simp [word_sums] at hp
    repeat (cases hp with | inl h => cases h; simp at hi; repeat (cases hi <;> try omega) | inr hp => _)
    -- Last case: ([22, 0, 11, 19, 25], 34)
    cases hp
    simp at hi
    repeat (cases hi <;> try omega)
  )

def main : IO Unit := do
  saveAllBackendsAutoTimed alpha_puzzle
