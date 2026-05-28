/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shalev Wengrowsky
-/

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Probability.Distributions.Uniform

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 1972, Problem 3

n digits, none of them 0, are randomly (and independently) generated,
find the probability that their product is divisible by 10.
-/

namespace Usa1972P3

abbrev Digit := Fin 9
abbrev DigitSeq (n : ℕ) := Fin n → Digit

noncomputable def unifDistN (n : ℕ) := PMF.uniformOfFintype (DigitSeq n)


def to_nat_digit : Digit → ℕ := fun d ↦ d + 1
def is_good_seq {n : ℕ} (s : DigitSeq n) := 10 ∣ ∏a, to_nat_digit (s a)
def good_seqs {n : ℕ} := {s : DigitSeq n | is_good_seq s}

snip begin

abbrev HasEven {n : ℕ} (s : DigitSeq n) : Prop := ∃ i, Even (to_nat_digit (s i))
abbrev HasFive {n : ℕ} (s : DigitSeq n) : Prop := ∃ i, to_nat_digit (s i) = 5
abbrev NoEven {n : ℕ} (s : DigitSeq n) : Prop := ∀ i, ¬ Even (to_nat_digit (s i))
abbrev NoFive {n : ℕ} (s : DigitSeq n) : Prop := ∀ i, to_nat_digit (s i) ≠ 5

def allDigitsEquiv {n : ℕ} (P : Digit → Prop) [DecidablePred P] :
    {s : DigitSeq n // ∀ i, P (s i)} ≃ (Fin n → {d : Digit // P d}) where
  toFun s := fun i => ⟨s.1 i, s.2 i⟩
  invFun f := ⟨fun i => (f i).1, fun i => (f i).2⟩
  left_inv s := by ext i; rfl
  right_inv f := by ext i; rfl

lemma card_all_digits {n : ℕ} (P : Digit → Prop) [DecidablePred P] :
    Fintype.card {s : DigitSeq n // ∀ i, P (s i)} =
      Fintype.card {d : Digit // P d} ^ n := by
  simpa [Fintype.card_fun] using Fintype.card_congr (allDigitsEquiv (n := n) P)

lemma digit_dvd_five_iff (d : Digit) : 5 ∣ to_nat_digit d ↔ to_nat_digit d = 5 := by
  fin_cases d <;> norm_num [to_nat_digit]

lemma card_digits_noFive :
    Fintype.card {d : Digit // to_nat_digit d ≠ 5} = 8 := by decide

lemma card_digits_noEven :
    Fintype.card {d : Digit // ¬ Even (to_nat_digit d)} = 5 := by decide

lemma card_digits_noFive_noEven :
    Fintype.card {d : Digit // to_nat_digit d ≠ 5 ∧ ¬ Even (to_nat_digit d)} = 4 := by decide

lemma ten_dvd_iff_two_and_five (m : ℕ) : 10 ∣ m ↔ 2 ∣ m ∧ 5 ∣ m := by
  constructor
  · intro h
    exact ⟨dvd_trans (by norm_num : 2 ∣ 10) h, dvd_trans (by norm_num : 5 ∣ 10) h⟩
  · rintro ⟨h2, h5⟩
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 5) h2 h5
    simpa using h

lemma two_dvd_prod_iff_hasEven {n : ℕ} (s : DigitSeq n) :
    2 ∣ ∏ a, to_nat_digit (s a) ↔ HasEven s := by
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
  simp [HasEven, even_iff_two_dvd]

lemma five_dvd_prod_iff_hasFive {n : ℕ} (s : DigitSeq n) :
    5 ∣ ∏ a, to_nat_digit (s a) ↔ HasFive s := by
  rw [Prime.dvd_finsetProd_iff Nat.prime_five.prime]
  simp [HasFive, digit_dvd_five_iff]

lemma is_good_seq_iff_hasEven_hasFive {n : ℕ} (s : DigitSeq n) :
    is_good_seq s ↔ HasEven s ∧ HasFive s := by
  rw [is_good_seq, ten_dvd_iff_two_and_five,
    two_dvd_prod_iff_hasEven, five_dvd_prod_iff_hasFive]

lemma card_all_noFive (n : ℕ) :
    Fintype.card {s : DigitSeq n // NoFive s} = 8 ^ n := by
  simpa only [NoFive, card_digits_noFive] using
    (card_all_digits (n := n) fun d => to_nat_digit d ≠ 5)

lemma card_all_noEven (n : ℕ) :
    Fintype.card {s : DigitSeq n // NoEven s} = 5 ^ n := by
  simpa only [NoEven, card_digits_noEven] using
    (card_all_digits (n := n) fun d => ¬ Even (to_nat_digit d))

lemma card_all_noFive_noEven (n : ℕ) :
    Fintype.card {s : DigitSeq n // NoFive s ∧ NoEven s} = 4 ^ n := by
  simpa only [NoFive, NoEven, forall_and, card_digits_noFive_noEven] using
    (card_all_digits (n := n)
      fun d => to_nat_digit d ≠ 5 ∧ ¬ Even (to_nat_digit d))

-- Inclusion-exclusion on the bad events.
lemma card_good_balance (n : ℕ) :
    {s : DigitSeq n | is_good_seq s}.ncard + 8 ^ n + 5 ^ n = 9 ^ n + 4 ^ n := by
  classical
  let G := Finset.univ.filter (fun s : DigitSeq n => is_good_seq s)
  let A := Finset.univ.filter (fun s : DigitSeq n => NoFive s)
  let B := Finset.univ.filter (fun s : DigitSeq n => NoEven s)
  have hGcompl : G = (A ∪ B)ᶜ := by
    ext s
    simp [G, A, B, NoFive, NoEven, HasFive, HasEven, is_good_seq_iff_hasEven_hasFive]
    tauto
  have hGcard : {s : DigitSeq n | is_good_seq s}.ncard = G.card := by
    rw [Set.ncard_eq_toFinset_card]
    congr
    ext s
    simp [G]
  have hAcard : A.card = 8 ^ n := by
    rw [← card_all_noFive n]
    exact (Fintype.card_of_subtype A (by intro s; simp [A, NoFive])).symm
  have hBcard : B.card = 5 ^ n := by
    rw [← card_all_noEven n]
    exact (Fintype.card_of_subtype B (by intro s; simp [B, NoEven])).symm
  have hABcard : (A ∩ B).card = 4 ^ n := by
    rw [← card_all_noFive_noEven n]
    exact (Fintype.card_of_subtype (A ∩ B) (by intro s; simp [A, B, NoFive, NoEven])).symm
  have hUcard : Fintype.card (DigitSeq n) = 9 ^ n := by
    simp [DigitSeq, Digit]
  have hcompl := Finset.card_add_card_compl (A ∪ B)
  have hunion := Finset.card_union_add_card_inter A B
  rw [hGcard, hGcompl] at *
  rw [hAcard, hBcard, hABcard] at hunion
  rw [hUcard] at hcompl
  omega

lemma ennreal_eq_sub_sub_of_add_add_eq {a b c d : ENNReal}
    (hb : b ≠ ⊤) (hc : c ≠ ⊤) (h : (a + c) + b = d) : a = d - b - c := by
  exact ENNReal.eq_sub_of_add_eq hc (ENNReal.eq_sub_of_add_eq hb h)

snip end

noncomputable determine solution (n : ℕ) : ENNReal :=
  1 + (4 / 9) ^ n - (8 / 9) ^ n - (5 / 9) ^ n

problem usa1972_p3 (n : ℕ) (_hn : 1 < n) :
  (unifDistN n).toOuterMeasure good_seqs = solution n := by
  classical
  have hcard := card_good_balance n
  rw [unifDistN, PMF.uniformOfFintype, PMF.toOuterMeasure_uniformOfFinset_apply]
  simp [solution, good_seqs]
  have hcard_enn :
      ((({x : DigitSeq n | is_good_seq x} : Finset (DigitSeq n)).card + 8 ^ n + 5 ^ n : ℕ) : ENNReal) =
        (9 ^ n + 4 ^ n : ℕ) := by
    rw [Set.ncard_eq_toFinset_card] at hcard
    exact_mod_cast (by simpa [Set.toFinset_setOf] using hcard)
  have hdiv := congrArg (fun x : ENNReal => x / ((9 : ENNReal) ^ n)) hcard_enn
  simp [ENNReal.add_div, ENNReal.div_self] at hdiv
  -- Convert counts to probabilities.
  have hbalance :
      (↑({x : DigitSeq n | is_good_seq x} : Finset (DigitSeq n)).card / (9 : ENNReal) ^ n +
          (5 / 9 : ENNReal) ^ n) + (8 / 9 : ENNReal) ^ n =
        1 + (4 / 9 : ENNReal) ^ n := by
    simpa [div_eq_mul_inv, mul_pow, ENNReal.inv_pow, add_assoc, add_comm, add_left_comm] using hdiv
  exact ennreal_eq_sub_sub_of_add_add_eq (by finiteness) (by finiteness) hbalance

end Usa1972P3
