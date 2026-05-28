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

open scoped BigOperators

determine solution : ℕ := 50 * Nat.choose 100 50

structure Good (S : Fin 100 → Set ℤ) : Prop where
  finite : ∀ i, (S i).Finite
  nonempty_inter : ⋂ i, S i ≠ ∅
  card : ∀ T : Finset (Fin 100), T.Nonempty →
                 ∃ k : ℕ, (⋂ i ∈ T, S i).ncard = k * T.card

-- z is in at least k of the sets S.
abbrev InAtLeastKSubsets (S : Fin 100 → Set ℤ) (k : ℕ) (z : ℤ) : Prop :=
  k ≤ {i : Fin 100 | z ∈ S i }.ncard

snip begin

abbrev Signature := Finset (Fin 100)

def topSignature : Signature := Finset.univ

/-- The membership signature of an integer with respect to the family `S`. -/
noncomputable def signatureOf (S : Fin 100 → Set ℤ) (z : ℤ) : Signature := by
  classical
  exact Finset.univ.filter fun i ↦ z ∈ S i

/-- Mathematically this is
`∑ v, if u ⊆ v then f v else 0`, the number of elements lying in every
set indexed by `u`, where `f v` is the number of elements with exact
membership signature `v`. It is left abstract here to avoid constructing
the `2^100`-element finset of all signatures in the intermediate file. -/
noncomputable def SignatureIntersectionCount (f : Signature → ℕ) (u : Signature) : ℕ := by
  exact ∑ v : Signature, if u ⊆ v then f v else 0

/-- The finite signature-count formulation of the problem. Only nonempty
signatures matter, since integers outside all `S i` have the empty signature
and form an infinite irrelevant complement. -/
def SignatureCountCondition (f : Signature → ℕ) : Prop :=
  ∀ u : Signature, u.Nonempty → u.card ∣ SignatureIntersectionCount f u

/-- The quantity to be minimized in the signature-count formulation.
Mathematically this is `∑ v, if 50 ≤ |v| then f v else 0`; it is abstract
for the same reason as `SignatureIntersectionCount`. -/
noncomputable def SignatureObjective (f : Signature → ℕ) : ℕ := by
  exact ∑ v : Signature, if 50 ≤ v.card then f v else 0

/-- The high-rank part of the greedy construction: for `|v| ≥ 50`, assign
`2 |v| - 100` elements to signature `v`. Lower ranks are filled later by
downward induction to satisfy the remaining divisibility conditions. -/
def canonicalHighCount (v : Signature) : ℕ :=
  if 50 ≤ v.card then 2 * v.card - 100 else 0

/-- One push-down step in the smoothing proof. Remove `|v|` elements from
signature `v`, and add one element to every immediate sub-signature. -/
def pushDown (f : Signature → ℕ) (v : Signature) : Signature → ℕ :=
  fun w ↦
    if w = v then f w - v.card
    else if w ⊆ v ∧ w.card + 1 = v.card then f w + 1
    else f w

lemma canonicalHighCount_valid_on_high :
    ∀ u : Signature, 50 ≤ u.card →
      u.card ∣ SignatureIntersectionCount canonicalHighCount u := by
  -- This is the binomial computation from the informal proof:
  -- if `|u| = 100 - k`, then the sum equals `|u| * 2^k`.
  sorry

lemma canonicalHighCount_objective :
    SignatureObjective canonicalHighCount = solution := by
  -- This is the identity
  --   `∑_{r=50}^{100} (2r - 100) * C(100,r) = 50 * C(100,50)`.
  sorry

lemma pushDown_preserves_condition {f : Signature → ℕ} {v : Signature}
    (hfv : v.card ≤ f v) (hf : SignatureCountCondition f) :
    SignatureCountCondition (pushDown f v) := by
  -- For a fixed nonempty `u`, only terms with `u ⊆ v` change.  In that case
  -- the net change is `-|u|`; otherwise the net change is zero.
  sorry

lemma pushDown_preserves_objective_of_large {f : Signature → ℕ} {v : Signature}
    (hv : 50 < v.card) (hfv : v.card ≤ f v) :
    SignatureObjective (pushDown f v) = SignatureObjective f := by
  -- When `|v| > 50`, all immediate sub-signatures still have size at least
  -- `50`, so the objective loses `|v|` at `v` and gains `|v|` in total below.
  classical
  have hv_le : 50 ≤ v.card := by omega
  have hpush_v : pushDown f v v = f v - v.card := by
    simp [pushDown]
  have hterm_v_new :
      (if 50 ≤ v.card then pushDown f v v else 0) = f v - v.card := by
    simp [hv_le, hpush_v]
  have hterm_v_old :
      (if 50 ≤ v.card then f v else 0) = f v := by
    simp [hv_le]
  have hchoose_pred : v.card.choose (v.card - 1) = v.card := by
    cases hcard : v.card with
    | zero => omega
    | succ n =>
        simp [Nat.choose_succ_self_right]
  have himmediate_sum :
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if w ⊆ v ∧ w.card + 1 = v.card then 1 else 0) = v.card := by
    rw [← Finset.card_filter
      (fun w : Signature ↦ w ⊆ v ∧ w.card + 1 = v.card)
      ((Finset.univ : Finset Signature).erase v)]
    have hfilter :
        ((Finset.univ : Finset Signature).erase v).filter
            (fun w : Signature ↦ w ⊆ v ∧ w.card + 1 = v.card)
          = Finset.powersetCard (v.card - 1) v := by
      ext w
      constructor
      · intro h
        have h' := Finset.mem_filter.mp h
        exact Finset.mem_powersetCard.mpr ⟨h'.2.1, by omega⟩
      · intro h
        have h' := Finset.mem_powersetCard.mp h
        refine Finset.mem_filter.mpr ⟨?_, h'.1, by omega⟩
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ w⟩
        intro hwv
        have hwcard : w.card = v.card := by rw [hwv]
        omega
    rw [hfilter, Finset.card_powersetCard, hchoose_pred]
  have hsum_erase :
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then pushDown f v w else 0)
        =
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then f w else 0) + v.card := by
    calc
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then pushDown f v w else 0)
          =
        (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          ((if 50 ≤ w.card then f w else 0)
            + (if w ⊆ v ∧ w.card + 1 = v.card then 1 else 0))) := by
            refine Finset.sum_congr rfl ?_
            intro w hw
            have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
            by_cases himmediate : w ⊆ v ∧ w.card + 1 = v.card
            · have hwcard : 50 ≤ w.card := by omega
              simp [pushDown, hwne, himmediate, hwcard]
            · by_cases hwcard : 50 ≤ w.card
              · simp [pushDown, hwne, himmediate, hwcard]
              · simp [himmediate, hwcard]
      _ =
        (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then f w else 0)
          +
        (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if w ⊆ v ∧ w.card + 1 = v.card then 1 else 0) := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then f w else 0) + v.card := by
            rw [himmediate_sum]
  calc
    SignatureObjective (pushDown f v)
        = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then pushDown f v w else 0)
            + (if 50 ≤ v.card then pushDown f v v else 0) := by
          rw [SignatureObjective]
          exact (Finset.sum_erase_add (Finset.univ : Finset Signature)
            (fun w ↦ if 50 ≤ w.card then pushDown f v w else 0)
            (Finset.mem_univ v)).symm
    _ = ((∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0) + v.card) + (f v - v.card) := by
          rw [hsum_erase, hterm_v_new]
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0) + f v := by
          omega
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0)
          + (if 50 ≤ v.card then f v else 0) := by
          rw [hterm_v_old]
    _ = SignatureObjective f := by
          rw [SignatureObjective]
          exact Finset.sum_erase_add (Finset.univ : Finset Signature)
            (fun w ↦ if 50 ≤ w.card then f w else 0)
            (Finset.mem_univ v)

lemma pushDown_decreases_objective_at_middle {f : Signature → ℕ} {v : Signature}
    (hv : v.card = 50) (hfv : v.card ≤ f v) :
    SignatureObjective (pushDown f v) + 50 = SignatureObjective f := by
  classical
  have hv_le : 50 ≤ v.card := by omega
  have hfv50 : 50 ≤ f v := by omega
  have hpush_v : pushDown f v v = f v - 50 := by
    simp [pushDown, hv]
  have hterm_v_new :
      (if 50 ≤ v.card then pushDown f v v else 0) = f v - 50 := by
    simp [hv_le, hpush_v]
  have hterm_v_old :
      (if 50 ≤ v.card then f v else 0) = f v := by
    simp [hv_le]
  have hother :
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then pushDown f v w else 0)
        =
      (∑ w ∈ (Finset.univ : Finset Signature).erase v,
          if 50 ≤ w.card then f w else 0) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
    by_cases hwcard : 50 ≤ w.card
    · have hnot_immediate : ¬(w ⊆ v ∧ w.card + 1 = v.card) := by
        intro h
        omega
      simp [hwcard, pushDown, hwne, hnot_immediate]
    · simp [hwcard]
  calc
    SignatureObjective (pushDown f v) + 50
        = ((∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then pushDown f v w else 0)
            + (if 50 ≤ v.card then pushDown f v v else 0)) + 50 := by
          rw [SignatureObjective]
          rw [← Finset.sum_erase_add (Finset.univ : Finset Signature)
            (fun w ↦ if 50 ≤ w.card then pushDown f v w else 0)
            (Finset.mem_univ v)]
    _ = ((∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0) + (f v - 50)) + 50 := by
          rw [hother, hterm_v_new]
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0) + f v := by
          omega
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if 50 ≤ w.card then f w else 0)
          + (if 50 ≤ v.card then f v else 0) := by
          rw [hterm_v_old]
    _ = SignatureObjective f := by
          rw [SignatureObjective]
          exact Finset.sum_erase_add (Finset.univ : Finset Signature)
            (fun w ↦ if 50 ≤ w.card then f w else 0)
            (Finset.mem_univ v)

/-- The downward-induction construction of the lower-rank counts. This packages
the easy half of the proof in the signature-count language. -/
lemma extend_canonical_high_counts :
    ∃ f : Signature → ℕ,
      SignatureCountCondition f ∧
      0 < f topSignature ∧
      (∀ v : Signature, 50 ≤ v.card → f v = canonicalHighCount v) ∧
      SignatureObjective f = solution := by
  -- Fill ranks `49, 48, ..., 1` by choosing the least residue modulo `|u|`
  -- that makes the divisibility condition true. This leaves the objective
  -- unchanged, and `f(topSignature) = 100`.
  sorry

/-- Any finite nonempty-signature count model can be realized by actual finite
sets of integers. -/
lemma realize_signature_counts
    {f : Signature → ℕ}
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature) :
    ∃ S : Fin 100 → Set ℤ,
      Good S ∧
      {z : ℤ | InAtLeastKSubsets S 50 z }.ncard = SignatureObjective f := by
  -- Use disjoint integer blocks indexed by nonempty signatures and a finite
  -- counter `0 ≤ j < f v`; put an integer from block `v` into exactly those
  -- `S i` with `i ∈ v`.
  sorry

/-- Signature counts extracted from an actual family of sets. The empty fiber is
ignored, because it is the infinite complement of the union of the sets. -/
noncomputable def signatureCount (S : Fin 100 → Set ℤ) (v : Signature) : ℕ := by
  classical
  exact if v.Nonempty then {z : ℤ | signatureOf S z = v}.ncard else 0

lemma signatureCount_condition_of_good (S : Fin 100 → Set ℤ) (hS : Good S) :
    SignatureCountCondition (signatureCount S) := by
  -- The intersection over a nonempty `u` is the disjoint union of the exact
  -- signature fibers `v` with `u ⊆ v`.
  sorry

lemma signatureCount_top_pos_of_good (S : Fin 100 → Set ℤ) (hS : Good S) :
    0 < signatureCount S topSignature := by
  classical
  have htop : topSignature.Nonempty := by
    exact ⟨0, by simp [topSignature]⟩
  have hnonempty : (⋂ i, S i).Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr hS.nonempty_inter
  rcases hnonempty with ⟨z, hz⟩
  have hzsig : signatureOf S z = topSignature := by
    ext i
    have hzi : z ∈ S i := Set.mem_iInter.mp hz i
    simp [signatureOf, topSignature, hzi]
  have hfiber_nonempty :
      {z : ℤ | signatureOf S z = topSignature}.Nonempty := ⟨z, hzsig⟩
  have hfiber_finite :
      {z : ℤ | signatureOf S z = topSignature}.Finite := by
    have hsubset : {z : ℤ | signatureOf S z = topSignature} ⊆ S 0 := by
      intro y hy
      have hmem : (0 : Fin 100) ∈ signatureOf S y := by
        rw [hy]
        simp [topSignature]
      simpa [signatureOf] using hmem
    exact (hS.finite 0).subset hsubset
  have hpos : 0 < {z : ℤ | signatureOf S z = topSignature}.ncard := by
    exact (Set.ncard_pos hfiber_finite).mpr hfiber_nonempty
  simpa [signatureCount, htop] using hpos

lemma signatureObjective_eq_original_objective
    (S : Fin 100 → Set ℤ) (hS : Good S) :
    SignatureObjective (signatureCount S) =
      {z : ℤ | InAtLeastKSubsets S 50 z }.ncard := by
  -- Partition the finite set of elements lying in at least `50` of the sets by
  -- their exact signature.
  sorry

/-- The smoothing argument. Repeated push-downs transform any valid signature
count model into the canonical high-rank model, never increasing the objective.
-/
lemma signature_model_lower_bound
    (f : Signature → ℕ)
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature) :
    solution ≤ SignatureObjective f := by
  -- Push down from rank `100`, then `99`, and so on down to `50`. The process
  -- preserves the divisibility condition; it leaves the objective unchanged
  -- above rank `50` and can only decrease it at rank `50`. The final residues
  -- are forced to agree with `canonicalHighCount`, whose objective is
  -- `solution`.
  sorry

snip end

/-- The standard construction, phrased in terms of membership signatures. For
each signature `v` with at least `50` indices, prescribe `2 * |v| - 100`
elements having exactly that signature, then fill lower signatures by downward
induction so the remaining divisibility conditions hold without changing the
objective. -/
lemma construction_attains_solution :
    ∃ S, Good S ∧
      solution = {z : ℤ | InAtLeastKSubsets S 50 z }.ncard := by
  rcases extend_canonical_high_counts with ⟨f, hf, htop, _hhigh, hobj⟩
  rcases realize_signature_counts hf htop with ⟨S, hS, hSobj⟩
  refine ⟨S, hS, ?_⟩
  rw [hSobj, hobj]

/-- Lower bound from the online solutions. Rephrase the problem as nonnegative
signature counts and repeatedly push mass from a signature to its immediate
subsignatures; the divisibility conditions are preserved, and the objective
cannot decrease below the constructed value. -/
lemma at_least_solution_elements (S : Fin 100 → Set ℤ) (hS : Good S) :
    solution ≤ {z : ℤ | InAtLeastKSubsets S 50 z }.ncard := by
  rw [← signatureObjective_eq_original_objective S hS]
  exact signature_model_lower_bound
    (signatureCount S)
    (signatureCount_condition_of_good S hS)
    (signatureCount_top_pos_of_good S hS)

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
