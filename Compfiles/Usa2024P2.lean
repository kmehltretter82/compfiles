/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Data.Set.Card
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2024, Problem 2

Let S₁, S₂, ..., S₁₀₀ be finite sets of integers whose intersection
is not empty. For each non-empty T ⊆ {S₁, S₂, ..., S₁₀₀}, the size of
the intersection of the sets in T is a multiple of the number of
sets in T. What is the least possible number of elements that are in
at least 50 sets?
-/

namespace Usa2024P2

determine solution : ℕ := 50 * Nat.choose 100 50

structure Good (S : Fin 100 → Set ℤ) : Prop where
  finite : ∀ i, (S i).Finite
  nonempty_inter : ⋂ i, S i ≠ ∅
  card : ∀ T : Finset (Fin 100), T.Nonempty →
                 ∃ k : ℕ, (⋂ i ∈ T, S i).ncard = k * T.card

-- z is in at least k of the sets S.
abbrev InAtLeastKSubsets (S : Fin 100 → Set ℤ) (k : ℕ) (z : ℤ) : Prop :=
  k ≤ {i : Fin 100 | z ∈ S i }.ncard

/-- The standard construction, phrased in terms of membership signatures. For
each signature `v` with at least `50` indices, prescribe `2 * |v| - 100`
elements having exactly that signature, then fill lower signatures by downward
induction so the remaining divisibility conditions hold without changing the
objective. -/
lemma construction_attains_solution :
    ∃ S, Good S ∧
      solution = {z : ℤ | InAtLeastKSubsets S 50 z }.ncard := by
  sorry

/-- Lower bound from the online solutions. Rephrase the problem as nonnegative
signature counts and repeatedly push mass from a signature to its immediate
subsignatures; the divisibility conditions are preserved, and the objective
cannot decrease below the constructed value. -/
lemma at_least_solution_elements (S : Fin 100 → Set ℤ) (hS : Good S) :
    solution ≤ {z : ℤ | InAtLeastKSubsets S 50 z }.ncard := by
  sorry

problem usa2024_p2 :
    IsLeast
      { k | ∃ S, Good S ∧
             k = {z : ℤ | InAtLeastKSubsets S 50 z }.ncard } solution :=
  by
    constructor
    · exact construction_attains_solution
    · intro k hk
      rcases hk with ⟨S, hS, hk⟩
      rw [hk]
      exact at_least_solution_elements S hS


end Usa2024P2
