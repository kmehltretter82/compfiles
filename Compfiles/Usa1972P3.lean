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

lemma card_all_digits {n : ℕ} (P : Digit → Prop) [DecidablePred P] {k : ℕ}
    (hP : Fintype.card {d : Digit // P d} = k) :
    Fintype.card {s : DigitSeq n // ∀ i, P (s i)} = k ^ n := by
  rw [Fintype.card_congr (allDigitsEquiv (n := n) P)]
  rw [Fintype.card_fun]
  rw [hP]
  simp

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
  exact card_all_digits (fun d => to_nat_digit d ≠ 5) card_digits_noFive

lemma card_all_noEven (n : ℕ) :
    Fintype.card {s : DigitSeq n // NoEven s} = 5 ^ n := by
  exact card_all_digits (fun d => ¬ Even (to_nat_digit d)) card_digits_noEven

lemma card_all_noFive_noEven (n : ℕ) :
    Fintype.card {s : DigitSeq n // NoFive s ∧ NoEven s} = 4 ^ n := by
  let e : {s : DigitSeq n // NoFive s ∧ NoEven s} ≃
      {s : DigitSeq n // ∀ i, to_nat_digit (s i) ≠ 5 ∧ ¬ Even (to_nat_digit (s i))} :=
    { toFun := fun s => ⟨s.1, fun i => ⟨s.2.1 i, s.2.2 i⟩⟩
      invFun := fun s => ⟨s.1, ⟨fun i => (s.2 i).1, fun i => (s.2 i).2⟩⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  rw [Fintype.card_congr e]
  exact card_all_digits (fun d => to_nat_digit d ≠ 5 ∧ ¬ Even (to_nat_digit d))
    card_digits_noFive_noEven

lemma card_good_balance (n : ℕ) :
    {s : DigitSeq n | is_good_seq s}.ncard + 8 ^ n + 5 ^ n = 9 ^ n + 4 ^ n := by
  classical
  let G := Finset.univ.filter (fun s : DigitSeq n => is_good_seq s)
  let A := Finset.univ.filter (fun s : DigitSeq n => NoFive s)
  let B := Finset.univ.filter (fun s : DigitSeq n => NoEven s)
  have hG : G = (A ∪ B)ᶜ := by
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
  rw [hGcard, hG] at *
  rw [hAcard, hBcard, hABcard] at hunion
  rw [hUcard] at hcompl
  omega

snip end

noncomputable determine solution (n : ℕ) : ENNReal :=
  1 + (4 / 9) ^ n - (8 / 9) ^ n - (5 / 9) ^ n 

problem usa1972_p3 (n : ℕ) (_hn : 1 < n) :
  (unifDistN n).toOuterMeasure good_seqs = solution n := by
  classical
  have hcard := card_good_balance n
  rw [unifDistN, PMF.toOuterMeasure_uniformOfFintype_apply]
  simp [solution, good_seqs]
  have hcard' :
      Fintype.card {x : DigitSeq n // is_good_seq x} + 8 ^ n + 5 ^ n =
        9 ^ n + 4 ^ n := by
    rw [Set.ncard_eq_toFinset_card] at hcard
    have hgood :
        Fintype.card {x : DigitSeq n // is_good_seq x} =
          ({x : DigitSeq n | is_good_seq x} : Finset (DigitSeq n)).card :=
      Fintype.card_of_subtype _ (by intro x; simp)
    simpa [Set.toFinset_setOf, hgood] using hcard
  let g := Fintype.card {x : DigitSeq n // is_good_seq x}
  have hcard_enn : ((g : ℕ) + 8 ^ n + 5 ^ n : ENNReal) = (9 ^ n + 4 ^ n : ℕ) := by
    exact_mod_cast hcard'
  have hdiv := congrArg (fun x : ENNReal => x / ((9 : ENNReal) ^ n)) hcard_enn
  simp [g, ENNReal.add_div, ENNReal.div_self] at hdiv
  simp [div_eq_mul_inv, mul_pow, ENNReal.inv_pow] at hdiv ⊢
  have hB : ((8 : ENNReal) ^ n * (9 : ENNReal)⁻¹ ^ n) ≠ ⊤ := by finiteness
  have hC : ((5 : ENNReal) ^ n * (9 : ENNReal)⁻¹ ^ n) ≠ ⊤ := by finiteness
  have hdiv' :
      (↑(Fintype.card {x : DigitSeq n // is_good_seq x}) *
          (9 : ENNReal)⁻¹ ^ n +
        (5 : ENNReal) ^ n * (9 : ENNReal)⁻¹ ^ n) +
          (8 : ENNReal) ^ n * (9 : ENNReal)⁻¹ ^ n =
        1 + (4 : ENNReal) ^ n * (9 : ENNReal)⁻¹ ^ n := by
    simpa [add_assoc, add_comm, add_left_comm] using hdiv
  have hAC :
      ↑(Fintype.card {x : DigitSeq n // is_good_seq x}) *
          (9 : ENNReal)⁻¹ ^ n +
        (5 : ENNReal) ^ n * (9 : ENNReal)⁻¹ ^ n =
          (1 + (4 : ENNReal) ^ n * (9 : ENNReal)⁻¹ ^ n) -
            (8 : ENNReal) ^ n * (9 : ENNReal)⁻¹ ^ n :=
    ENNReal.eq_sub_of_add_eq hB hdiv'
  exact ENNReal.eq_sub_of_add_eq hC hAC

end Usa1972P3
