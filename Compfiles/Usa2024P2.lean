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

lemma ncard_preimage_eq_sum_fibers
    {α β : Type} [Fintype β] [DecidableEq β]
    (g : α → β) (p : β → Prop) [DecidablePred p]
    (hfin : {a : α | p (g a)}.Finite) :
    {a : α | p (g a)}.ncard =
      ∑ b : β, if p b then {a : α | g a = b}.ncard else 0 := by
  classical
  let e : ↑({a : α | p (g a)}) ≃
      Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1})) :=
    { toFun := fun a => ⟨⟨g a.1, a.2⟩, ⟨a.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, by
        show p (g x.2.1)
        rw [x.2.2]
        exact x.1.2⟩
      left_inv := by
        intro a
        ext
        rfl
      right_inv := by
        intro x
        cases x with
        | mk b a =>
          ext
          · exact a.2
          · rfl }
  have hfiber_fin : ∀ b : ↑({b : β | p b}), ({a : α | g a = b.1}).Finite := by
    intro b
    exact hfin.subset (by
      intro a ha
      show p (g a)
      rw [ha]
      exact b.2)
  letI := hfin.fintype
  letI : Fintype ↑({b : β | p b}) := inferInstance
  letI (b : ↑({b : β | p b})) : Fintype ↑({a : α | g a = b.1}) :=
    (hfiber_fin b).fintype
  letI : Fintype
      (Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1}))) :=
    inferInstance
  have hAcard :
      {a : α | p (g a)}.ncard = Fintype.card ↑({a : α | p (g a)}) := by
    rw [Set.ncard_eq_toFinset_card ({a : α | p (g a)}) hfin]
    exact hfin.card_toFinset
  have hsigma :
      Fintype.card
        (Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1})))
        = ∑ b : ↑({b : β | p b}), ({a : α | g a = b.1}).ncard := by
    calc
      Fintype.card
          (Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1})))
          = ∑ b : ↑({b : β | p b}), Fintype.card ↑({a : α | g a = b.1}) := by
            exact Fintype.card_sigma
      _ = ∑ b : ↑({b : β | p b}), ({a : α | g a = b.1}).ncard := by
        refine Finset.sum_congr rfl ?_
        intro b _
        rw [Set.ncard_eq_toFinset_card ({a : α | g a = b.1}) (hfiber_fin b)]
        exact (hfiber_fin b).card_toFinset.symm
  calc
    {a : α | p (g a)}.ncard = Fintype.card ↑({a : α | p (g a)}) := hAcard
    _ =
        Fintype.card
          (Sigma (fun b : ↑({b : β | p b}) => ↑({a : α | g a = b.1}))) := by
          exact Fintype.card_congr e
    _ = ∑ b : ↑({b : β | p b}), ({a : α | g a = b.1}).ncard := hsigma
    _ = ∑ b : β, if p b then {a : α | g a = b}.ncard else 0 := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_subtype ((Finset.univ : Finset β).filter p) ?_
        (fun b => ({a : α | g a = b}).ncard)]
      intro b
      simp

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

lemma immediate_supersets_count {u v : Signature} (huv : u ⊆ v) :
    (∑ w ∈ (Finset.univ : Finset Signature).erase v,
        if u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card then 1 else 0) =
      v.card - u.card := by
  classical
  let missing : Finset Signature := Finset.image (fun a : Fin 100 => v.erase a) (v \ u)
  have hfilter :
      ((Finset.univ : Finset Signature).erase v).filter
          (fun w : Signature => u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card)
        = missing := by
    ext w
    constructor
    · intro hw
      have hw' := Finset.mem_filter.mp hw
      have huw : u ⊆ w := hw'.2.1
      have hwv : w ⊆ v := hw'.2.2.1
      have hwcard : w.card + 1 = v.card := hw'.2.2.2
      have hlt : w.card < v.card := by omega
      rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨a, hav, haw⟩
      have hau : a ∉ u := fun ha => haw (huw ha)
      refine Finset.mem_image.mpr ⟨a, ?_, ?_⟩
      · exact Finset.mem_sdiff.mpr ⟨hav, hau⟩
      · symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          have hxv : x ∈ v := hwv hx
          have hxa : x ≠ a := by
            intro hxa
            exact haw (by simpa [hxa] using hx)
          exact Finset.mem_erase.mpr ⟨hxa, hxv⟩
        · rw [Finset.card_erase_of_mem hav]
          omega
    · intro hw
      rcases Finset.mem_image.mp hw with ⟨a, ha, rfl⟩
      have hav : a ∈ v := (Finset.mem_sdiff.mp ha).1
      have hau : a ∉ u := (Finset.mem_sdiff.mp ha).2
      have hvcpos : 0 < v.card := Finset.card_pos.mpr ⟨a, hav⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro h
        have : a ∉ v.erase a := by simp
        exact this (by rw [h]; exact hav)
      · refine ⟨?_, ?_, ?_⟩
        · intro x hx
          exact Finset.mem_erase.mpr ⟨fun hxa => hau (by simpa [hxa] using hx), huv hx⟩
        · intro x hx
          exact (Finset.mem_erase.mp hx).2
        · rw [Finset.card_erase_of_mem hav]
          omega
  rw [← Finset.card_filter
    (fun w : Signature => u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card)
    ((Finset.univ : Finset Signature).erase v)]
  rw [hfilter]
  have himage_card : missing.card = (v \ u).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    change v.erase a = v.erase b at hab
    by_contra hne
    have hmem : a ∈ v.erase b := by
      exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_sdiff.mp ha).1⟩
    have hmem' : a ∈ v.erase a := by
      rw [hab]
      exact hmem
    have : a ∉ v.erase a := by simp
    exact this hmem'
  rw [himage_card, Finset.card_sdiff_of_subset huv]

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
  classical
  intro u hu
  by_cases huv : u ⊆ v
  · have hucard_le_vcard : u.card ≤ v.card := Finset.card_le_card huv
    have hchange :
        SignatureIntersectionCount (pushDown f v) u + u.card =
          SignatureIntersectionCount f u := by
      rw [SignatureIntersectionCount, SignatureIntersectionCount]
      rw [← Finset.sum_erase_add (Finset.univ : Finset Signature)
        (fun w => if u ⊆ w then pushDown f v w else 0) (Finset.mem_univ v)]
      rw [← Finset.sum_erase_add (Finset.univ : Finset Signature)
        (fun w => if u ⊆ w then f w else 0) (Finset.mem_univ v)]
      have herase :
          (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then pushDown f v w else 0)
            =
          (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then f w else 0) + (v.card - u.card) := by
        calc
          (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then pushDown f v w else 0)
              =
            (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              ((if u ⊆ w then f w else 0)
                + (if u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card then 1 else 0))) := by
              refine Finset.sum_congr rfl ?_
              intro w hw
              have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
              by_cases huw : u ⊆ w
              · by_cases himm : w ⊆ v ∧ w.card + 1 = v.card
                · simp [pushDown, hwne, huw, himm]
                · simp [pushDown, hwne, huw, himm]
              · have hnot : ¬(u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card) := by
                  exact fun h => huw h.1
                simp [huw]
          _ =
            (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then f w else 0) +
            (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w ∧ w ⊆ v ∧ w.card + 1 = v.card then 1 else 0) := by
              rw [Finset.sum_add_distrib]
          _ =
            (∑ w ∈ (Finset.univ : Finset Signature).erase v,
              if u ⊆ w then f w else 0) + (v.card - u.card) := by
              rw [immediate_supersets_count huv]
      have hpush_v : pushDown f v v = f v - v.card := by simp [pushDown]
      simp [huv, hpush_v]
      rw [herase]
      omega
    have hold : u.card ∣ SignatureIntersectionCount f u := hf u hu
    rw [← hchange] at hold
    exact (Nat.dvd_add_self_right).mp hold
  · have hchange :
        SignatureIntersectionCount (pushDown f v) u = SignatureIntersectionCount f u := by
      rw [SignatureIntersectionCount, SignatureIntersectionCount]
      refine Finset.sum_congr rfl ?_
      intro w _
      by_cases huw : u ⊆ w
      · have hwne : w ≠ v := by
          intro hwv
          exact huv (by simpa [hwv] using huw)
        have hnot : ¬(w ⊆ v ∧ w.card + 1 = v.card) := by
          intro h
          exact huv (fun i hi => h.1 (huw hi))
        simp [pushDown, huw, hwne, hnot]
      · simp [huw]
    rw [hchange]
    exact hf u hu

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

/-- The contribution to the intersection count of `u` coming from strict
supersignatures only. This is the part that is already known when lower ranks
are filled by downward induction. -/
noncomputable def strictSupersetContribution (f : Signature → ℕ) (u : Signature) : ℕ :=
  ∑ w : Signature, if u ⊂ w then f w else 0

/-- One step of the construction: fill all signatures of cardinality `k` with
the least residue that makes their own intersection count divisible by `k`.
Higher ranks are left unchanged, so this can be iterated for `k = 49, ..., 1`.
-/
noncomputable def fillRank (k : ℕ) (f : Signature → ℕ) : Signature → ℕ :=
  fun v ↦
    if v.card = k then
      let s := strictSupersetContribution f v
      (v.card - s % v.card) % v.card
    else f v

/-- If `s` is the already-fixed strict-superset contribution, this residue is
chosen exactly so that `residue + s` is divisible by `d`. -/
lemma dvd_complement_mod_add {d s : ℕ} (hd : 0 < d) :
    d ∣ ((d - s % d) % d) + s := by
  let r := s % d
  have hrlt : r < d := by simpa [r] using Nat.mod_lt s hd
  by_cases hr0 : r = 0
  · have hsmod : s % d = 0 := by simpa [r] using hr0
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [hsmod]
  · have hres : (d - r) % d = d - r := Nat.mod_eq_of_lt (by omega)
    refine ⟨s / d + 1, ?_⟩
    calc
      ((d - s % d) % d) + s = (d - r) + s := by simp [r, hres]
      _ = (d - r) + (d * (s / d) + r) := by rw [Nat.div_add_mod s d]
      _ = d * (s / d + 1) := by
        rw [show (d - r) + (d * (s / d) + r) =
            ((d - r) + r) + d * (s / d) by omega]
        rw [Nat.sub_add_cancel (le_of_lt hrlt)]
        ring

lemma fillRank_eq_of_card {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hv : v.card = k) :
    fillRank k f v =
      let s := strictSupersetContribution f v
      (v.card - s % v.card) % v.card := by
  simp [fillRank, hv]

lemma fillRank_eq_self_of_card_ne {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hv : v.card ≠ k) : fillRank k f v = f v := by
  simp [fillRank, hv]

lemma fillRank_eq_self_of_card_gt {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hv : k < v.card) : fillRank k f v = f v := by
  exact fillRank_eq_self_of_card_ne (by omega)

lemma fillRank_eq_self_of_card_lt {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hv : v.card < k) : fillRank k f v = f v := by
  exact fillRank_eq_self_of_card_ne (by omega)

lemma fillRank_eq_self_of_high {k : ℕ} {f : Signature → ℕ} {v : Signature}
    (hk : k < 50) (hv : 50 ≤ v.card) : fillRank k f v = f v := by
  exact fillRank_eq_self_of_card_gt (by omega)

lemma fillRank_eq_self_on_supersets_of_card_lt {k : ℕ} {f : Signature → ℕ}
    {u w : Signature} (hu : k < u.card) (huw : u ⊆ w) :
    fillRank k f w = f w := by
  apply fillRank_eq_self_of_card_gt
  exact lt_of_lt_of_le hu (Finset.card_le_card huw)

lemma strictSupersetContribution_congr {f g : Signature → ℕ} {u : Signature}
    (h : ∀ w : Signature, u ⊂ w → f w = g w) :
    strictSupersetContribution f u = strictSupersetContribution g u := by
  unfold strictSupersetContribution
  refine Finset.sum_congr rfl ?_
  intro w _
  by_cases huw : u ⊂ w
  · simp [huw, h w huw]
  · simp [huw]

/-- Split the intersection count of `u` into the exact `u` term and all strict
supersignatures. This is the triangularity that makes the downward construction
work. -/
lemma SignatureIntersectionCount_eq_self_add_strict
    (f : Signature → ℕ) (u : Signature) :
    SignatureIntersectionCount f u = f u + strictSupersetContribution f u := by
  classical
  let A : Signature → ℕ := fun w ↦ if u ⊆ w then f w else 0
  let B : Signature → ℕ := fun w ↦ if u ⊂ w then f w else 0
  have hsum_erase :
      (∑ w ∈ (Finset.univ : Finset Signature).erase u, A w) =
        ∑ w ∈ (Finset.univ : Finset Signature).erase u, B w := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hne : w ≠ u := (Finset.mem_erase.mp hw).1
    by_cases huw : u ⊆ w
    · have hss : u ⊂ w := Finset.ssubset_iff_subset_ne.mpr ⟨huw, hne.symm⟩
      simp [A, B, huw, hss]
    · have hnss : ¬ u ⊂ w := fun h => huw h.1
      simp [A, B, huw, hnss]
  have hstrict_erase :
      strictSupersetContribution f u =
        ∑ w ∈ (Finset.univ : Finset Signature).erase u, B w := by
    rw [strictSupersetContribution]
    rw [← Finset.sum_erase_add (Finset.univ : Finset Signature) B (Finset.mem_univ u)]
    have hnss : ¬ u ⊂ u := by exact irrefl u
    simp [B, hnss]
  calc
    SignatureIntersectionCount f u =
        (∑ w ∈ (Finset.univ : Finset Signature).erase u, A w) + A u := by
          rw [SignatureIntersectionCount]
          exact (Finset.sum_erase_add (Finset.univ : Finset Signature) A
            (Finset.mem_univ u)).symm
    _ = (∑ w ∈ (Finset.univ : Finset Signature).erase u, A w) + f u := by
          simp [A]
    _ = f u + (∑ w ∈ (Finset.univ : Finset Signature).erase u, B w) := by
          rw [hsum_erase, Nat.add_comm]
    _ = f u + strictSupersetContribution f u := by
          rw [hstrict_erase]

lemma SignatureIntersectionCount_fillRank_of_card_gt {k : ℕ} {f : Signature → ℕ}
    {u : Signature} (hu : k < u.card) :
    SignatureIntersectionCount (fillRank k f) u = SignatureIntersectionCount f u := by
  classical
  rw [SignatureIntersectionCount, SignatureIntersectionCount]
  refine Finset.sum_congr rfl ?_
  intro w _
  by_cases huw : u ⊆ w
  · rw [if_pos huw, if_pos huw, fillRank_eq_self_on_supersets_of_card_lt hu huw]
  · simp [huw]

lemma fillRank_self_add_strictSupersetContribution_dvd {k : ℕ} {f : Signature → ℕ}
    {u : Signature} (hu : u.card = k) (hupos : 0 < u.card) :
    u.card ∣ fillRank k f u + strictSupersetContribution f u := by
  rw [fillRank_eq_of_card hu]
  exact dvd_complement_mod_add hupos

/-- The new rank `k` is made valid by construction; strict supersets are
unchanged because they have larger cardinality. -/
lemma fillRank_satisfies_rank {k : ℕ} {f : Signature → ℕ} {u : Signature}
    (hu : u.card = k) (hupos : 0 < u.card) :
    u.card ∣ SignatureIntersectionCount (fillRank k f) u := by
  rw [SignatureIntersectionCount_eq_self_add_strict]
  have hcongr :
      strictSupersetContribution (fillRank k f) u =
        strictSupersetContribution f u := by
    apply strictSupersetContribution_congr
    intro w huw
    exact fillRank_eq_self_of_card_gt (by
      have hcard := Finset.card_lt_card huw
      omega)
  rw [hcongr]
  exact fillRank_self_add_strictSupersetContribution_dvd hu hupos

/-- Filling rank `k` cannot disturb intersection counts for already-completed
ranks above `k`. -/
lemma fillRank_preserves_completed_ranks {k : ℕ} {f : Signature → ℕ}
    (hf : ∀ u : Signature, u.Nonempty → k < u.card →
      u.card ∣ SignatureIntersectionCount f u) :
    ∀ u : Signature, u.Nonempty → k < u.card →
      u.card ∣ SignatureIntersectionCount (fillRank k f) u := by
  intro u hu hku
  rw [SignatureIntersectionCount_fillRank_of_card_gt hku]
  exact hf u hu hku

/-- The induction step for the eventual construction: after filling rank `k`,
all nonempty signatures of rank at least `k` satisfy their divisibility
condition. -/
lemma fillRank_extends_completed_ranks {k : ℕ} {f : Signature → ℕ}
    (hf : ∀ u : Signature, u.Nonempty → k < u.card →
      u.card ∣ SignatureIntersectionCount f u) :
    ∀ u : Signature, u.Nonempty → k ≤ u.card →
      u.card ∣ SignatureIntersectionCount (fillRank k f) u := by
  intro u hu hku
  by_cases huk : u.card = k
  · exact fillRank_satisfies_rank huk (Finset.card_pos.mpr hu)
  · apply fillRank_preserves_completed_ranks hf
    · exact hu
    · omega

/-- High signatures are not touched during the lower-rank filling process, so
the objective stays the canonical objective. The final proof should apply this
lemma at each step for `k < 50`. -/
lemma SignatureObjective_fillRank_of_low {k : ℕ} {f : Signature → ℕ}
    (hk : k < 50) :
    SignatureObjective (fillRank k f) = SignatureObjective f := by
  rw [SignatureObjective, SignatureObjective]
  refine Finset.sum_congr rfl ?_
  intro v _
  by_cases hv : 50 ≤ v.card
  · rw [fillRank_eq_self_of_high hk hv]
  · simp [hv]

/-- Placeholder for the finite iteration over `k = 49, 48, ..., 1`. A convenient
implementation is to define this by `Nat.iterate` or a fold over
`List.range 49`, then use `fillRank_extends_completed_ranks` as the loop
invariant and `SignatureObjective_fillRank_of_low` for the objective. -/
lemma lower_rank_filling_exists :
    ∃ f : Signature → ℕ,
      (∀ u : Signature, u.Nonempty →
        u.card ∣ SignatureIntersectionCount f u) ∧
      (∀ v : Signature, 50 ≤ v.card → f v = canonicalHighCount v) ∧
      SignatureObjective f = SignatureObjective canonicalHighCount := by
  -- Start from `canonicalHighCount`. The invariant after finishing rank `k` is:
  --   every nonempty `u` with `k ≤ u.card` is valid,
  --   every high-rank `v` still has the canonical count,
  --   the objective is unchanged.
  -- The base case at rank `50` is `canonicalHighCount_valid_on_high`; the step
  -- from `k+1` to `k` is `fillRank_extends_completed_ranks`.
  sorry

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
  classical
  intro u hu
  rcases hS.card u hu with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [mul_comm k u.card] at hk
  rw [← hk]
  symm
  have hinter_eq :
      (⋂ i ∈ u, S i) = {z : ℤ | u ⊆ signatureOf S z} := by
    ext z
    constructor
    · intro hz
      intro i hi
      have hzi : z ∈ S i := Set.mem_iInter₂.mp hz i hi
      simp [signatureOf, hzi]
    · intro hz
      exact Set.mem_iInter₂.mpr (fun i hi => by
        have hsig : i ∈ signatureOf S z := hz hi
        simpa [signatureOf] using hsig)
  have hinter_finite : (⋂ i ∈ u, S i).Finite := by
    rcases hu with ⟨i, hi⟩
    exact (hS.finite i).subset (by
      intro z hz
      exact Set.mem_iInter₂.mp hz i hi)
  calc
    (⋂ i ∈ u, S i).ncard
        = {z : ℤ | u ⊆ signatureOf S z}.ncard := by rw [hinter_eq]
    _ = ∑ v : Signature, if u ⊆ v then {z : ℤ | signatureOf S z = v}.ncard else 0 := by
          exact ncard_preimage_eq_sum_fibers (signatureOf S) (fun v : Signature => u ⊆ v)
            (by simpa [← hinter_eq] using hinter_finite)
    _ = SignatureIntersectionCount (signatureCount S) u := by
          rw [SignatureIntersectionCount]
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases huv : u ⊆ v
          · have hvnonempty : v.Nonempty := by
              rcases hu with ⟨i, hi⟩
              exact ⟨i, huv hi⟩
            simp [huv, signatureCount, hvnonempty]
          · simp [huv]

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
  classical
  have hsig_card :
      ∀ z : ℤ, {i : Fin 100 | z ∈ S i}.ncard = (signatureOf S z).card := by
    intro z
    have hfin : {i : Fin 100 | z ∈ S i}.Finite :=
      Set.finite_univ.subset (by intro i _; simp)
    rw [Set.ncard_eq_toFinset_card _ hfin]
    simp [signatureOf]
  have hobj_set :
      {z : ℤ | InAtLeastKSubsets S 50 z}
        = {z : ℤ | 50 ≤ (signatureOf S z).card} := by
    ext z
    simp [InAtLeastKSubsets, hsig_card z]
  have hunion_finite : (⋃ i, S i).Finite := Set.finite_iUnion hS.finite
  have hobj_finite : {z : ℤ | 50 ≤ (signatureOf S z).card}.Finite := by
    refine hunion_finite.subset ?_
    intro z hz
    have hpos : 0 < {i : Fin 100 | z ∈ S i}.ncard := by
      have hsigpos : 0 < (signatureOf S z).card := lt_of_lt_of_le (by norm_num) hz
      rw [hsig_card z]
      exact hsigpos
    have hnonempty : {i : Fin 100 | z ∈ S i}.Nonempty := by
      exact (Set.ncard_pos (Set.finite_univ.subset (by intro i _; simp))).mp hpos
    rcases hnonempty with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  calc
    SignatureObjective (signatureCount S)
        = ∑ v : Signature, if 50 ≤ v.card then {z : ℤ | signatureOf S z = v}.ncard else 0 := by
          rw [SignatureObjective]
          refine Finset.sum_congr rfl ?_
          intro v _
          by_cases hv : 50 ≤ v.card
          · have hvnonempty : v.Nonempty := by
              cases v.eq_empty_or_nonempty with
              | inl hempty =>
                  exfalso
                  simpa [hempty] using hv
              | inr h => exact h
            simp [hv, signatureCount, hvnonempty]
          · simp [hv]
    _ = {z : ℤ | 50 ≤ (signatureOf S z).card}.ncard := by
          exact (ncard_preimage_eq_sum_fibers (signatureOf S)
            (fun v : Signature => 50 ≤ v.card) hobj_finite).symm
    _ = {z : ℤ | InAtLeastKSubsets S 50 z}.ncard := by rw [hobj_set]

lemma topSignature_card : topSignature.card = 100 := by
  simp [topSignature]

lemma topSignature_nonempty : topSignature.Nonempty := by
  exact ⟨0, by simp [topSignature]⟩

lemma eq_topSignature_of_card_eq_100 {v : Signature} (hv : v.card = 100) :
    v = topSignature := by
  apply Finset.eq_univ_of_card
  simp [hv]

lemma card_lt_100_of_ne_topSignature {v : Signature} (hvt : v ≠ topSignature) :
    v.card < 100 := by
  have hle : v.card ≤ 100 := by
    have h := Finset.card_le_univ v
    simpa using h
  by_contra hnot
  have hv : v.card = 100 := by omega
  exact hvt (eq_topSignature_of_card_eq_100 hv)

lemma canonicalHighCount_top : canonicalHighCount topSignature = 100 := by
  simp [canonicalHighCount, topSignature]

lemma canonicalHighCount_lt_card_of_high_ne_top {v : Signature}
    (hv : 50 ≤ v.card) (hvt : v ≠ topSignature) :
    canonicalHighCount v < v.card := by
  have hlt : v.card < 100 := card_lt_100_of_ne_topSignature hvt
  simp [canonicalHighCount, hv]
  omega

lemma canonicalHighCount_le_card_of_high {v : Signature} (hv : 50 ≤ v.card) :
    canonicalHighCount v ≤ v.card := by
  by_cases htop : v = topSignature
  · subst htop
    simp [canonicalHighCount, topSignature]
  · exact le_of_lt (canonicalHighCount_lt_card_of_high_ne_top hv htop)

lemma iterate_pushDown_self (f : Signature → ℕ) (v : Signature) (n : ℕ) :
    (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) v =
      f v - n * v.card := by
  induction n with
  | zero => simp [Nat.iterate]
  | succ n ih =>
      rw [Function.iterate_succ']
      simp [pushDown, ih]
      rw [Nat.sub_sub]
      congr 1
      ring

lemma iterate_pushDown_condition {f : Signature → ℕ} {v : Signature} (n : ℕ)
    (hsteps : n * v.card ≤ f v) (hf : SignatureCountCondition f) :
    SignatureCountCondition
      (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) := by
  induction n with
  | zero => simpa [Nat.iterate]
  | succ n ih =>
      rw [Function.iterate_succ']
      change SignatureCountCondition
        (pushDown ((Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f)) v)
      apply pushDown_preserves_condition
      · rw [iterate_pushDown_self]
        have hn : (n + 1) * v.card = n * v.card + v.card := by ring
        omega
      · apply ih
        have : n * v.card ≤ (n + 1) * v.card := by nlinarith [Nat.zero_le v.card]
        omega

lemma iterate_pushDown_objective_le {f : Signature → ℕ} {v : Signature} (n : ℕ)
    (hv : 50 ≤ v.card) (hsteps : n * v.card ≤ f v) :
    SignatureObjective
        (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) ≤
      SignatureObjective f := by
  induction n with
  | zero => simp [Nat.iterate]
  | succ n ih =>
      rw [Function.iterate_succ']
      change SignatureObjective
          (pushDown ((Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f)) v) ≤
        SignatureObjective f
      have hprev : n * v.card ≤ f v := by
        have : n * v.card ≤ (n + 1) * v.card := by nlinarith [Nat.zero_le v.card]
        omega
      have henough : v.card ≤
          (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) v := by
        rw [iterate_pushDown_self]
        have hn : (n + 1) * v.card = n * v.card + v.card := by ring
        omega
      by_cases hlarge : 50 < v.card
      · rw [pushDown_preserves_objective_of_large hlarge henough]
        exact ih hprev
      · have hmid : v.card = 50 := by omega
        have hdrop := pushDown_decreases_objective_at_middle hmid henough
        have hle_step : SignatureObjective (pushDown
            (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) v) ≤
            SignatureObjective
              (Nat.iterate (fun g : Signature → ℕ => pushDown g v) n f) := by
          omega
        exact le_trans hle_step (ih hprev)

lemma pushDown_to_canonical_count {f : Signature → ℕ} {v : Signature}
    (hf : SignatureCountCondition f) (hv : 50 ≤ v.card)
    (hcan_le : canonicalHighCount v ≤ f v)
    (hdiv : v.card ∣ f v - canonicalHighCount v) :
    let n := (f v - canonicalHighCount v) / v.card
    let g := Nat.iterate (fun h : Signature → ℕ => pushDown h v) n f
    SignatureCountCondition g ∧ SignatureObjective g ≤ SignatureObjective f ∧
      g v = canonicalHighCount v := by
  dsimp
  let n := (f v - canonicalHighCount v) / v.card
  have hmul : n * v.card = f v - canonicalHighCount v := by
    dsimp [n]
    exact Nat.div_mul_cancel hdiv
  have hsteps : n * v.card ≤ f v := by omega
  refine ⟨iterate_pushDown_condition n hsteps hf, iterate_pushDown_objective_le n hv hsteps, ?_⟩
  rw [iterate_pushDown_self, hmul]
  omega

lemma high_signature_count_forced_after_supersets_normalized
    {f : Signature → ℕ} {v : Signature}
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature)
    (hv : 50 ≤ v.card)
    (hstrict : ∀ w : Signature, v ⊂ w → f w = canonicalHighCount w) :
    canonicalHighCount v ≤ f v ∧ v.card ∣ f v - canonicalHighCount v := by
  -- At this point the strict supersets of `v` have already been smoothed.
  -- Splitting the intersection count at `v` into the `v`-term and strict
  -- supersets gives a congruence for `f v` modulo `|v|`. For non-top `v`,
  -- the canonical count is the unique residue in `[0, |v|)`. For
  -- `topSignature`, `htop` upgrades divisibility by `100` to the lower bound
  -- `100 ≤ f topSignature`.
  sorry

lemma smooth_high_signatures_to_canonical
    (f : Signature → ℕ)
    (hf : SignatureCountCondition f) (htop : 0 < f topSignature) :
    ∃ g : Signature → ℕ,
      SignatureCountCondition g ∧
      SignatureObjective g ≤ SignatureObjective f ∧
      (∀ v : Signature, 50 ≤ v.card → g v = canonicalHighCount v) := by
  -- Process ranks `100, 99, ..., 50`. At a signature `v`, all strict
  -- supersets have already been normalized, so
  -- `high_signature_count_forced_after_supersets_normalized` says exactly how
  -- many complete `|v|`-blocks can be pushed down while leaving the canonical
  -- high-rank residue. The iteration helpers above package the repeated
  -- push-down at one fixed signature; the remaining bookkeeping is the finite
  -- induction over the high-rank signatures ordered by descending cardinality.
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
  classical
  rcases smooth_high_signatures_to_canonical f hf htop with
    ⟨g, _hg, hobj_le, hcanonical⟩
  have hgobj : SignatureObjective g = SignatureObjective canonicalHighCount := by
    rw [SignatureObjective, SignatureObjective]
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases hv : 50 ≤ v.card
    · simp [hv, hcanonical v hv]
    · simp [hv]
  calc
    solution = SignatureObjective canonicalHighCount := canonicalHighCount_objective.symm
    _ = SignatureObjective g := hgobj.symm
    _ ≤ SignatureObjective f := hobj_le

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
