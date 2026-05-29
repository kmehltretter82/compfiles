/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Bounds.Basic

import ProblemExtraction

problem_file {
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2025P5.lean"
}

/-!
# International Mathematical Olympiad 2025, Problem 5

Alice and Bazza are playing the *inekoalaty game*, a two-player game
whose rules depend on a positive number λ known to both players. On
the nth turn of the game (starting with n = 1) the following happens:

 * If n is odd, Alice chooses a nonnegative real number xₙ such that

                    x₁ + x₂ + ... + xₙ ≤ λn

 * If n is even, Bazza chooses a nonnegative real number xₙ such that

                   x₁² + x₂² + .. + xₙ² ≤ n.

If a player cannot choose a suitable n, the game ends and the other
player wins. If the game goes forever, neither player wins. All
chosen numbers are known to both players.

Determine all values of λ for which Alice has a winning strategy
and all those for which Bazza has a winning strategy.
-/

namespace Imo2025P5

/-- Whether all the numbers chosen are valid. -/
def ValidSeq (c : ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop := (∀ i : Fin n, 0 ≤ x i) ∧
  (∀ i : Fin n, Even (i : ℕ) → (∑ j ≤ i, x j) ≤ c * ((i : ℕ) + 1)) ∧
  (∀ i : Fin n, Odd (i : ℕ) → (∑ j ≤ i, (x j) ^ 2) ≤ ((i : ℕ) + 1))

/-- Whether a sequence of numbers chosen is a win for the given player (expressed as the 0-based
numbers of that player's moves, mod 2): the other player makes the first invalid move. -/
def Wins (c : ℝ) (p : ℕ) {n : ℕ} (x : Fin n → ℝ) : Prop := ∃ i : Fin n, (i : ℕ) % 2 ≠ p ∧
  IsLeast {j : Fin n | ¬ ValidSeq c (Fin.take ((j : ℕ) + 1)
    (Nat.succ_le_of_lt j.isLt) x)} i

/-- A strategy for a given player gives a choice of number in every position, with the convention
that invalid moves lose and the strategy's choices are ignored in cases where it is not that
player's turn, a previous move was invalid or the sequence of previous moves is not possible
under the strategy. -/
abbrev Strategy : Type := ⦃k : ℕ⦄ → (Fin k → ℝ) → ℝ

/-- Playing a strategy, k turns, against a given sequence of opponent moves (possibly not
valid). -/
def Strategy.play (s : Strategy) (p : ℕ) (opponentMoves : ℕ → ℝ) : (k : ℕ) → Fin k → ℝ
| 0 => Fin.elim0
| k + 1 => Fin.snoc (s.play p opponentMoves k)
    (if k % 2 = p then s (s.play p opponentMoves k) else opponentMoves k)

/-- Whether a strategy wins for the given player, against all possible opponent moves. -/
def Strategy.Winning (s : Strategy) (c : ℝ) (p : ℕ) : Prop :=
  ∀ opponentMoves : ℕ → ℝ, ∃ k : ℕ, Wins c p (s.play p opponentMoves k)

snip begin

noncomputable abbrev threshold : ℝ := 1 / Real.sqrt 2

lemma threshold_pos : 0 < threshold := by
  dsimp [threshold]
  positivity

lemma two_mul_threshold : 2 * threshold = Real.sqrt 2 := by
  dsimp [threshold]
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  rw [Real.sq_sqrt (by positivity)]

lemma threshold_le_sqrt_two : threshold ≤ Real.sqrt 2 := by
  rw [← two_mul_threshold]
  nlinarith [threshold_pos]

lemma threshold_mul_odd (r : ℕ) :
    threshold * (2 * (r : ℝ) + 1) = Real.sqrt 2 * (r : ℝ) + threshold := by
  rw [← two_mul_threshold]
  ring

lemma sqrt_two_mul_lt_c_mul_odd {c : ℝ} (hc : threshold < c) (r : ℕ) :
    Real.sqrt 2 * (r : ℝ) < c * (2 * (r : ℝ) + 1) := by
  have hmul : threshold * (2 * (r : ℝ) + 1) < c * (2 * (r : ℝ) + 1) :=
    mul_lt_mul_of_pos_right hc (by positivity)
  rw [← two_mul_threshold]
  nlinarith [threshold_pos]

lemma sqrt_two_mul_le_c_mul_odd {c : ℝ} (hc : threshold ≤ c) (r : ℕ) :
    Real.sqrt 2 * (r : ℝ) ≤ c * (2 * (r : ℝ) + 1) := by
  have hmul : threshold * (2 * (r : ℝ) + 1) ≤ c * (2 * (r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  rw [← two_mul_threshold]
  nlinarith [threshold_pos]

/-- Alice waits until turn `2 * k + 1`, then spends the remaining linear budget. -/
noncomputable def AliceTriggerStrategy (c : ℝ) (k₀ : ℕ) : Strategy := fun {k} x =>
  if k = 2 * k₀ then c * (((k + 1 : ℕ) : ℝ)) - ∑ i, x i else 0

/-- Bazza's largest-response strategy from the solution notes. -/
noncomputable def BazzaMaxStrategy : Strategy := fun {k} x =>
  if hk : 0 < k then Real.sqrt (2 - (x ⟨k - 1, Nat.sub_one_lt_of_lt hk⟩) ^ 2) else 0

lemma Strategy.take_play (s : Strategy) (p : ℕ) (opponentMoves : ℕ → ℝ)
    {m n : ℕ} (h : m ≤ n) :
    Fin.take m h (s.play p opponentMoves n) = s.play p opponentMoves m := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero h
      subst hm
      simp [Strategy.play]
  | succ n ih =>
      by_cases hmn : m ≤ n
      · rw [← ih hmn]
        ext i
        have hi_lt_n : (i : ℕ) < n := lt_of_lt_of_le i.isLt hmn
        have harg : (Fin.castLE h i).castLT hi_lt_n = Fin.castLE hmn i := by
          ext
          rfl
        simp [Strategy.play, Fin.take, Fin.snoc, hi_lt_n, harg]
      · have hm : m = n + 1 :=
          le_antisymm h (Nat.succ_le_of_lt (Nat.lt_of_not_ge hmn))
        subst hm
        simp

lemma Strategy.play_apply_eq_step (s : Strategy) (p : ℕ) (opponentMoves : ℕ → ℝ)
    {m n : ℕ} (h : m < n) :
    s.play p opponentMoves n ⟨m, h⟩ =
      s.play p opponentMoves (m + 1) ⟨m, Nat.lt_succ_self m⟩ := by
  have ht := congr_fun (Strategy.take_play s p opponentMoves (Nat.succ_le_of_lt h))
      ⟨m, Nat.lt_succ_self m⟩
  simpa [Fin.take] using ht

lemma Strategy.valid_before_first_bad (s : Strategy) (p : ℕ) (opponentMoves : ℕ → ℝ)
    {c : ℝ} {n : ℕ} {i : Fin n}
    (hleast : IsLeast {j : Fin n | ¬ ValidSeq c
      (Fin.take ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt) (s.play p opponentMoves n))} i) :
    ValidSeq c (s.play p opponentMoves (i : ℕ)) := by
  by_cases hi0 : (i : ℕ) = 0
  · rw [hi0]
    simp [Strategy.play, ValidSeq]
  · let j : Fin n := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    have hvalid_j : ValidSeq c
        (Fin.take ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)
          (s.play p opponentMoves n)) := by
      by_contra hbad_j
      exact (not_le_of_gt (Fin.lt_def.mpr (by
        dsimp [j]
        exact Nat.sub_one_lt hi0))) (hleast.2 hbad_j)
    rw [Strategy.take_play] at hvalid_j
    have hlen : (j : ℕ) + 1 = (i : ℕ) := by
      dsimp [j]
      exact Nat.sub_one_add_one hi0
    rwa [hlen] at hvalid_j

lemma Strategy.invalid_at_first_bad (s : Strategy) (p : ℕ) (opponentMoves : ℕ → ℝ)
    {c : ℝ} {n : ℕ} {i : Fin n}
    (hleast : IsLeast {j : Fin n | ¬ ValidSeq c
      (Fin.take ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt) (s.play p opponentMoves n))} i) :
    ¬ ValidSeq c (s.play p opponentMoves ((i : ℕ) + 1)) := by
  have hbad := hleast.1
  dsimp at hbad
  rwa [Strategy.take_play] at hbad

lemma Strategy.wins_of_forced_invalid (s : Strategy) (c : ℝ) (p : ℕ)
    (opponentMoves : ℕ → ℝ) {last : ℕ}
    (hbad_last : ¬ ValidSeq c (s.play p opponentMoves (last + 1)))
    (hvalid_step : ∀ m, m ≤ last → m % 2 = p →
      ValidSeq c (s.play p opponentMoves m) →
      ValidSeq c (s.play p opponentMoves (m + 1))) :
    Wins c p (s.play p opponentMoves (last + 1)) := by
  classical
  let bad : ℕ → Prop := fun m => ¬ ValidSeq c (s.play p opponentMoves (m + 1))
  let hbad_exists : ∃ m, bad m := ⟨last, hbad_last⟩
  let m : ℕ := Nat.find hbad_exists
  have hbad_m : bad m := Nat.find_spec hbad_exists
  have hm_le_last : m ≤ last := Nat.find_min' hbad_exists hbad_last
  let i : Fin (last + 1) := ⟨m, Nat.lt_succ_of_le hm_le_last⟩
  have hprev_valid : ValidSeq c (s.play p opponentMoves m) := by
    by_cases hm0 : m = 0
    · dsimp [m] at hm0 ⊢
      rw [hm0]
      simp [Strategy.play, ValidSeq]
    · have hnot_bad_pred : ¬ bad (m - 1) := by
        dsimp [m]
        exact Nat.find_min hbad_exists (Nat.sub_one_lt hm0)
      exact by
        by_contra hbad_prev
        exact hnot_bad_pred (by dsimp [bad]; rwa [Nat.sub_one_add_one hm0])
  have hm_not_p : m % 2 ≠ p := by
    intro hmparity
    exact hbad_m (hvalid_step m hm_le_last hmparity hprev_valid)
  refine ⟨i, ?_, ?_⟩
  · exact hm_not_p
  · constructor
    · dsimp [i]
      rw [Strategy.take_play]
      exact hbad_m
    · intro j hj
      dsimp [i, m]
      apply Nat.find_min'
      dsimp [bad] at hj ⊢
      rw [Strategy.take_play] at hj
      exact hj

lemma ValidSeq.init {c : ℝ} {n : ℕ} {x : Fin n → ℝ} {a : ℝ}
    (hx : ValidSeq c (Fin.snoc x a)) : ValidSeq c x := by
  rcases hx with ⟨hxnon, hxlin, hxsq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa using hxnon i.castSucc
  · intro i hi
    simpa [Fin.sum_Iic_castSucc] using hxlin i.castSucc (by simpa using hi)
  · intro i hi
    simpa [Fin.sum_Iic_castSucc] using hxsq i.castSucc (by simpa using hi)

lemma ValidSeq.snoc {c : ℝ} {n : ℕ} {x : Fin n → ℝ} {a : ℝ}
    (hx : ValidSeq c x) (ha : 0 ≤ a)
    (hlin : Even n → (∑ j, x j) + a ≤ c * ((n : ℝ) + 1))
    (hsq : Odd n → (∑ j, (x j) ^ 2) + a ^ 2 ≤ ((n : ℝ) + 1)) :
    ValidSeq c (Fin.snoc x a) := by
  rcases hx with ⟨hxnon, hxlin, hxsq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa using ha
    | cast i => simpa using hxnon i
  · intro i hi
    induction i using Fin.lastCases with
    | last =>
        change (∑ j ≤ (⊤ : Fin (n + 1)), (Fin.snoc x a) j) ≤ c * ((n : ℝ) + 1)
        rw [Finset.Iic_top]
        rw [Fin.sum_univ_castSucc]
        simpa using hlin (by simpa using hi)
    | cast i => simpa [Fin.sum_Iic_castSucc] using hxlin i (by simpa using hi)
  · intro i hi
    induction i using Fin.lastCases with
    | last =>
        change (∑ j ≤ (⊤ : Fin (n + 1)), (Fin.snoc x a) j ^ 2) ≤ ((n : ℝ) + 1)
        rw [Finset.Iic_top]
        rw [Fin.sum_univ_castSucc]
        simpa using hsq (by simpa using hi)
    | cast i => simpa [Fin.sum_Iic_castSucc] using hxsq i (by simpa using hi)

lemma two_mul_fin_val_lt (k : ℕ) (r : Fin k) : 2 * (r : ℕ) < 2 * k :=
  Nat.mul_lt_mul_of_pos_left r.isLt (by norm_num)

lemma two_mul_fin_val_add_one_lt (k : ℕ) (r : Fin k) : 2 * (r : ℕ) + 1 < 2 * k := by
  have hsucc : (r : ℕ) + 1 ≤ k := Nat.succ_le_of_lt r.isLt
  calc
    2 * (r : ℕ) + 1 < 2 * ((r : ℕ) + 1) := by
      rw [Nat.mul_succ]
      simp
    _ ≤ 2 * k := Nat.mul_le_mul_left 2 hsucc

lemma two_mul_succ_eq (k : ℕ) : 2 * k + 2 = 2 * (k + 1) := by
  rw [Nat.mul_succ]

lemma two_mul_lt_two_mul_succ (k : ℕ) : 2 * k < 2 * (k + 1) := by
  rw [← two_mul_succ_eq]
  exact Nat.lt_add_of_pos_right (by norm_num : 0 < 2)

lemma two_mul_add_one_lt_two_mul_succ (k : ℕ) : 2 * k + 1 < 2 * (k + 1) := by
  rw [← two_mul_succ_eq]
  simp

lemma sum_fin_two_mul_pair (k : ℕ) (f : Fin (2 * k) → ℝ) :
    (∑ i : Fin (2 * k), f i) =
      ∑ r : Fin k, (f ⟨2 * (r : ℕ), two_mul_fin_val_lt k r⟩ +
        f ⟨2 * (r : ℕ) + 1, two_mul_fin_val_add_one_lt k r⟩) := by
  induction k with
  | zero => simp
  | succ k ih =>
      change (∑ i : Fin (2 * k + 2), f (Fin.cast (two_mul_succ_eq k) i)) =
        ∑ r : Fin (k + 1),
          (f ⟨2 * (r : ℕ), two_mul_fin_val_lt (k + 1) r⟩ +
            f ⟨2 * (r : ℕ) + 1, two_mul_fin_val_add_one_lt (k + 1) r⟩)
      conv_rhs => rw [Fin.sum_univ_castSucc]
      rw [Fin.sum_univ_castSucc]
      rw [Fin.sum_univ_castSucc]
      let g : Fin (2 * k) → ℝ := fun i => f (Fin.cast (two_mul_succ_eq k)
        i.castSucc.castSucc)
      have ihg := ih g
      simp only [Fin.val_castSucc, Fin.val_last]
      change (∑ i : Fin (2 * k), g i) +
          f (Fin.last (2 * k)).castSucc + f (Fin.last (2 * k + 1)) =
        (∑ x : Fin k, (f ⟨2 * (x : ℕ), two_mul_fin_val_lt (k + 1) x.castSucc⟩ +
          f ⟨2 * (x : ℕ) + 1, two_mul_fin_val_add_one_lt (k + 1) x.castSucc⟩)) +
          (f ⟨2 * k, two_mul_lt_two_mul_succ k⟩ +
            f ⟨2 * k + 1, two_mul_add_one_lt_two_mul_succ k⟩)
      rw [ihg]
      simp [g]
      have hlast0 : (Fin.last (2 * k)).castSucc =
          (⟨2 * k, two_mul_lt_two_mul_succ k⟩ : Fin (2 * (k + 1))) := by
        ext
        simp
      have hlast1 : (Fin.last (2 * k + 1) : Fin (2 * k + 2)) =
          (⟨2 * k + 1, two_mul_add_one_lt_two_mul_succ k⟩ : Fin (2 * (k + 1))) := by
        ext
        simp
      rw [hlast0, hlast1]
      ring

lemma sum_fin_two_mul_odd_of_even_zero (k : ℕ) {x : Fin (2 * k) → ℝ}
    (hzero : ∀ i : Fin (2 * k), Even (i : ℕ) → x i = 0) :
    (∑ i : Fin (2 * k), x i) =
      ∑ r : Fin k, x ⟨2 * (r : ℕ) + 1, two_mul_fin_val_add_one_lt k r⟩ := by
  rw [sum_fin_two_mul_pair]
  apply Finset.sum_congr rfl
  intro r _hr
  have hz : x ⟨2 * (r : ℕ), two_mul_fin_val_lt k r⟩ = 0 :=
    hzero _ (by change Even (2 * (r : ℕ)); exact even_two_mul (r : ℕ))
  simp [hz]

lemma sum_fin_two_mul_sq_odd_of_even_zero (k : ℕ) {x : Fin (2 * k) → ℝ}
    (hzero : ∀ i : Fin (2 * k), Even (i : ℕ) → x i = 0) :
    (∑ i : Fin (2 * k), (x i) ^ 2) =
      ∑ r : Fin k, (x ⟨2 * (r : ℕ) + 1, two_mul_fin_val_add_one_lt k r⟩) ^ 2 := by
  rw [sum_fin_two_mul_pair]
  apply Finset.sum_congr rfl
  intro r _hr
  have hz : x ⟨2 * (r : ℕ), two_mul_fin_val_lt k r⟩ = 0 :=
    hzero _ (by change Even (2 * (r : ℕ)); exact even_two_mul (r : ℕ))
  simp [hz]

-- Cauchy bounds the sum when Alice's even-indexed moves are all zero.
lemma valid_even_zero_sum_le {c : ℝ} {r : ℕ} {x : Fin (2 * r) → ℝ}
    (hx : ValidSeq c x)
    (hzero : ∀ i : Fin (2 * r), Even (i : ℕ) → x i = 0) :
    (∑ i : Fin (2 * r), x i) ≤ Real.sqrt 2 * (r : ℝ) := by
  rcases hx with ⟨_hxnon, _hxlin, hxsq⟩
  rw [sum_fin_two_mul_odd_of_even_zero r hzero]
  let b : Fin r → ℝ := fun i => x ⟨2 * (i : ℕ) + 1, two_mul_fin_val_add_one_lt r i⟩
  have hcauchy :=
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin r)) b (fun _ => (1 : ℝ))
  have hsum_le :
      (∑ i : Fin r, b i) ≤ Real.sqrt (∑ i : Fin r, b i ^ 2) * Real.sqrt (r : ℝ) := by
    simpa [b] using hcauchy
  have hsq_all : (∑ i : Fin (2 * r), x i ^ 2) ≤ (2 * (r : ℕ) : ℝ) := by
    by_cases hr : r = 0
    · subst hr
      simp
    · let lastIdx : Fin (2 * r) := ⟨2 * r - 1,
        Nat.sub_one_lt (Nat.mul_ne_zero (by norm_num) hr)⟩
      have hlastodd : Odd ((lastIdx : Fin (2 * r)) : ℕ) := by
        change Odd (2 * r - 1)
        exact Nat.not_even_iff_odd.mp (by
          rw [even_iff_two_dvd]
          exact Nat.two_not_dvd_two_mul_sub_one (Nat.pos_of_ne_zero hr))
      have hs := hxsq lastIdx hlastodd
      have hIic : Finset.Iic lastIdx = Finset.univ := by
        ext j
        simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
        exact Fin.le_iff_val_le_val.mpr (by
          dsimp [lastIdx]
          exact Nat.le_pred_of_lt j.isLt)
      have hlast_cast : ((lastIdx : ℕ) : ℝ) + 1 = (2 * (r : ℕ) : ℝ) := by
        dsimp [lastIdx]
        rw [Nat.cast_sub (Nat.succ_le_iff.mpr
          (Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hr)))]
        norm_num
      rw [hIic] at hs
      simpa [hlast_cast, Nat.cast_mul] using hs
  have hsq_b : (∑ i : Fin r, b i ^ 2) ≤ (2 * (r : ℕ) : ℝ) := by
    rw [← sum_fin_two_mul_sq_odd_of_even_zero r hzero]
    exact hsq_all
  have hle_sqrt : Real.sqrt (∑ i : Fin r, b i ^ 2) ≤ Real.sqrt (2 * (r : ℝ)) := by
    exact Real.sqrt_le_sqrt (by simpa [Nat.cast_mul] using hsq_b)
  have hprod_le :
      Real.sqrt (∑ i : Fin r, b i ^ 2) * Real.sqrt (r : ℝ) ≤
        Real.sqrt (2 * (r : ℝ)) * Real.sqrt (r : ℝ) := by
    exact mul_le_mul_of_nonneg_right hle_sqrt (Real.sqrt_nonneg _)
  have hsqrt_prod : Real.sqrt (2 * (r : ℝ)) * Real.sqrt (r : ℝ) =
      Real.sqrt 2 * (r : ℝ) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * (r : ℝ))]
    rw [show 2 * (r : ℝ) * (r : ℝ) = 2 * (r : ℝ) ^ 2 by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
    rw [Real.sqrt_sq_eq_abs]
    simp
  calc
    (∑ i : Fin r, b i) ≤ Real.sqrt (∑ i : Fin r, b i ^ 2) * Real.sqrt (r : ℝ) := hsum_le
    _ ≤ Real.sqrt (2 * (r : ℝ)) * Real.sqrt (r : ℝ) := hprod_le
    _ = Real.sqrt 2 * (r : ℝ) := hsqrt_prod

lemma threshold_lt_of_alice_gap {c : ℝ} {k : ℕ}
    (hgap : Real.sqrt 2 * (k : ℝ) <
      c * (2 * (k : ℝ) + 1) - Real.sqrt (2 * (k : ℝ) + 2)) :
    threshold < c := by
  have hsum_lt : Real.sqrt 2 * (k : ℝ) + Real.sqrt (2 * (k : ℝ) + 2) <
      c * (2 * (k : ℝ) + 1) := by
    nlinarith
  have hsqrt2_le : Real.sqrt 2 ≤ Real.sqrt (2 * (k : ℝ) + 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [show 0 ≤ (k : ℝ) by positivity]
  have hthreshold_le_sqrt : threshold ≤ Real.sqrt (2 * (k : ℝ) + 2) := by
    rw [← two_mul_threshold] at hsqrt2_le
    nlinarith [threshold_pos]
  have hthr_le : threshold * (2 * (k : ℝ) + 1) ≤
      Real.sqrt 2 * (k : ℝ) + Real.sqrt (2 * (k : ℝ) + 2) := by
    rw [← two_mul_threshold]
    nlinarith [hthreshold_le_sqrt]
  have hmul_lt : threshold * (2 * (k : ℝ) + 1) < c * (2 * (k : ℝ) + 1) :=
    lt_of_le_of_lt hthr_le hsum_lt
  nlinarith [show 0 < 2 * (k : ℝ) + 1 by positivity]

lemma aliceTrigger_play_even_zero_before {c : ℝ} {k n : ℕ} (opponentMoves : ℕ → ℝ)
    (hn : n ≤ 2 * k) {i : Fin n} (hi_even : Even (i : ℕ)) :
    (AliceTriggerStrategy c k).play 0 opponentMoves n i = 0 := by
  have hlt : (i : ℕ) < n := i.isLt
  rw [Strategy.play_apply_eq_step (s := AliceTriggerStrategy c k) (p := 0)
    (opponentMoves := opponentMoves) hlt]
  have hmod : (i : ℕ) % 2 = 0 := Nat.even_iff.mp hi_even
  have hne : (i : ℕ) ≠ 2 * k := ne_of_lt (lt_of_lt_of_le i.isLt hn)
  rw [Strategy.play]
  have hlast : (⟨(i : ℕ), Nat.lt_succ_self (i : ℕ)⟩ : Fin ((i : ℕ) + 1)) =
      Fin.last (i : ℕ) := by
    ext
    simp
  rw [hlast]
  simp [AliceTriggerStrategy, hmod, hne]

lemma aliceTrigger_even_step_valid {c : ℝ} {k m : ℕ} (opponentMoves : ℕ → ℝ)
    (hc : threshold < c) (hmle : m ≤ 2 * k) (hmeven : Even m)
    (hprev : ValidSeq c ((AliceTriggerStrategy c k).play 0 opponentMoves m)) :
    ValidSeq c ((AliceTriggerStrategy c k).play 0 opponentMoves (m + 1)) := by
  obtain ⟨r, hm_eq⟩ : ∃ r, m = 2 * r := by
    rcases hmeven with ⟨r, rfl⟩
    exact ⟨r, by simp [two_mul]⟩
  subst m
  rw [Strategy.play]
  simp only [Nat.mul_mod_right, ↓reduceIte]
  by_cases htrigger : 2 * r = 2 * k
  · have hrk : r = k := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) htrigger
    subst r
    simp [AliceTriggerStrategy]
    refine ValidSeq.snoc hprev ?_ ?_ ?_
    · have hzero : ∀ i : Fin (2 * k), Even (i : ℕ) →
          (AliceTriggerStrategy c k).play 0 opponentMoves (2 * k) i = 0 :=
        fun i hi => aliceTrigger_play_even_zero_before (c := c) (k := k)
          (n := 2 * k) opponentMoves (le_refl _) (i := i) hi
      have hsum_le := valid_even_zero_sum_le hprev hzero
      have hlin_gt := sqrt_two_mul_lt_c_mul_odd hc k
      nlinarith [hsum_le, hlin_gt]
    · intro _heven
      norm_num [Nat.cast_mul, Nat.cast_add]
    · intro hodd
      exfalso
      exact Nat.not_even_iff_odd.mpr hodd (even_two_mul k)
  · simp [AliceTriggerStrategy, htrigger]
    refine ValidSeq.snoc hprev (by positivity) ?_ ?_
    · intro _heven
      have hzero : ∀ i : Fin (2 * r), Even (i : ℕ) →
          (AliceTriggerStrategy c k).play 0 opponentMoves (2 * r) i = 0 :=
        fun i hi => aliceTrigger_play_even_zero_before (c := c) (k := k)
          (n := 2 * r) opponentMoves hmle (i := i) hi
      have hsum_le := valid_even_zero_sum_le hprev hzero
      have hlin_gt := sqrt_two_mul_lt_c_mul_odd hc r
      norm_num [Nat.cast_mul]
      nlinarith [hsum_le, hlin_gt]
    · intro hodd
      exfalso
      exact Nat.not_even_iff_odd.mpr hodd (even_two_mul r)

lemma aliceTrigger_forced_invalid {c : ℝ} {k : ℕ} (opponentMoves : ℕ → ℝ)
    (hgap : Real.sqrt 2 * (k : ℝ) <
      c * (2 * (k : ℝ) + 1) - Real.sqrt (2 * (k : ℝ) + 2)) :
    ¬ ValidSeq c ((AliceTriggerStrategy c k).play 0 opponentMoves (2 * k + 2)) := by
  intro hfull
  -- The trigger move is larger than the square budget available on Bazza's next turn.
  have hprefix1 : ValidSeq c ((AliceTriggerStrategy c k).play 0 opponentMoves (2 * k + 1)) := by
    apply ValidSeq.init (a := opponentMoves (2 * k + 1))
    simpa [Strategy.play, Nat.add_mod] using hfull
  have hprefix0 : ValidSeq c ((AliceTriggerStrategy c k).play 0 opponentMoves (2 * k)) := by
    apply ValidSeq.init
    simpa [Strategy.play, AliceTriggerStrategy] using hprefix1
  have hzero : ∀ i : Fin (2 * k), Even (i : ℕ) →
      (AliceTriggerStrategy c k).play 0 opponentMoves (2 * k) i = 0 :=
    fun i hi => aliceTrigger_play_even_zero_before (c := c) (k := k)
      (n := 2 * k) opponentMoves (le_refl _) (i := i) hi
  have hsum_le := valid_even_zero_sum_le hprefix0 hzero
  let trigger : ℝ := c * (((2 * k + 1 : ℕ) : ℝ)) -
    ∑ i, (AliceTriggerStrategy c k).play 0 opponentMoves (2 * k) i
  have htrigger_gt : Real.sqrt (2 * (k : ℝ) + 2) < trigger := by
    dsimp [trigger]
    have hgap' : Real.sqrt 2 * (k : ℝ) <
        c * (((2 * k + 1 : ℕ) : ℝ)) - Real.sqrt (2 * (k : ℝ) + 2) := by
      simpa [Nat.cast_add, Nat.cast_mul] using hgap
    nlinarith [hsum_le, hgap']
  let y : Fin (2 * k + 2) → ℝ := (AliceTriggerStrategy c k).play 0 opponentMoves (2 * k + 2)
  have h2k_lt_2k2 : 2 * k < 2 * k + 2 :=
    Nat.lt_add_of_pos_right (by norm_num : 0 < 2)
  have htrigger_val : y ⟨2 * k, h2k_lt_2k2⟩ = trigger := by
    dsimp [y, trigger]
    rw [Strategy.play_apply_eq_step (s := AliceTriggerStrategy c k) (p := 0)
      (opponentMoves := opponentMoves) h2k_lt_2k2]
    rw [Strategy.play]
    have hlast : (⟨2 * k, Nat.lt_succ_self (2 * k)⟩ : Fin (2 * k + 1)) =
        Fin.last (2 * k) := by
      ext
      simp
    rw [hlast]
    simp [AliceTriggerStrategy]
  have hsq_le : (∑ j : Fin (2 * k + 2), y j ^ 2) ≤ 2 * (k : ℝ) + 2 := by
    have h := hfull.2.2 (Fin.last (2 * k + 1)) (by simp)
    change (∑ j ≤ (⊤ : Fin (2 * k + 2)), y j ^ 2) ≤
      (((2 * k + 1 : ℕ) : ℝ) + 1) at h
    rw [Finset.Iic_top] at h
    have h' : (∑ x : Fin (2 * k + 2),
        (AliceTriggerStrategy c k).play 0 opponentMoves (2 * k + 2) x ^ 2) ≤
        2 * (k : ℝ) + 1 + 1 := by
      simpa [Nat.cast_add, Nat.cast_mul] using h
    simpa [y] using (by nlinarith : (∑ x : Fin (2 * k + 2),
        (AliceTriggerStrategy c k).play 0 opponentMoves (2 * k + 2) x ^ 2) ≤
        2 * (k : ℝ) + 2)
  have htrigger_sq_le : trigger ^ 2 ≤ ∑ j : Fin (2 * k + 2), y j ^ 2 := by
    have hsingle : y ⟨2 * k, h2k_lt_2k2⟩ ^ 2 ≤ ∑ j : Fin (2 * k + 2), y j ^ 2 := by
      exact Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (by simp)
    simpa [htrigger_val] using hsingle
  have hM_lt : 2 * (k : ℝ) + 2 < trigger ^ 2 := by
    have htrigger_pos : 0 < trigger :=
      lt_of_le_of_lt (Real.sqrt_nonneg _) htrigger_gt
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * (k : ℝ) + 2),
      Real.sqrt_nonneg (2 * (k : ℝ) + 2)]
  nlinarith

lemma exists_alice_trigger_time {c : ℝ} (hc : threshold < c) :
    ∃ k : ℕ, Real.sqrt 2 * (k : ℝ) <
      c * (2 * (k : ℝ) + 1) - Real.sqrt (2 * (k : ℝ) + 2) := by
  let a : ℝ := 2 * c - Real.sqrt 2
  have ha : 0 < a := by
    dsimp [a]
    rw [← two_mul_threshold]
    nlinarith [hc]
  have hcpos : 0 < c := lt_trans threshold_pos hc
  have ha_sq_pos : 0 < a ^ 2 := sq_pos_of_pos ha
  obtain ⟨k, hk⟩ := exists_nat_gt (max (2 : ℝ) (4 / a ^ 2))
  have hk_two : (2 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hk_bound : 4 / a ^ 2 < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
  have hkpos : 0 < (k : ℝ) := by positivity
  have hfour_lt : 4 < a ^ 2 * (k : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_bound ha_sq_pos
    field_simp [ne_of_gt ha_sq_pos] at hmul
    nlinarith
  have hquad : 2 * (k : ℝ) + 2 < a ^ 2 * (k : ℝ) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hfour_lt hkpos]
  have hsqrt_lt : Real.sqrt (2 * (k : ℝ) + 2) < a * (k : ℝ) := by
    rw [Real.sqrt_lt]
    · nlinarith
    · positivity
    · positivity
  use k
  have hsum : Real.sqrt 2 * (k : ℝ) + Real.sqrt (2 * (k : ℝ) + 2) <
      c * (2 * (k : ℝ) + 1) := by
    have hsum' := add_lt_add_left hsqrt_lt (Real.sqrt 2 * (k : ℝ))
    dsimp [a] at hsum'
    nlinarith
  nlinarith

lemma aliceTriggerStrategy_winning {c : ℝ} {k : ℕ}
    (hgap : Real.sqrt 2 * (k : ℝ) <
      c * (2 * (k : ℝ) + 1) - Real.sqrt (2 * (k : ℝ) + 2)) :
    (AliceTriggerStrategy c k).Winning c 0 := by
  intro opponentMoves
  have hc : threshold < c := threshold_lt_of_alice_gap hgap
  refine ⟨2 * k + 2, Strategy.wins_of_forced_invalid (AliceTriggerStrategy c k) c 0
    opponentMoves ?_ ?_⟩
  · simpa using aliceTrigger_forced_invalid (c := c) (k := k) opponentMoves hgap
  · intro m hmle hmparity hprev
    exact aliceTrigger_even_step_valid (c := c) (k := k) opponentMoves hc
      (by grind) (Nat.even_iff.mpr hmparity) hprev

lemma alice_winning_of_threshold_lt {c : ℝ} (hc : threshold < c) :
    ∃ s : Strategy, s.Winning c 0 := by
  obtain ⟨k, hk⟩ := exists_alice_trigger_time hc
  exact ⟨AliceTriggerStrategy c k, aliceTriggerStrategy_winning hk⟩

lemma pair_sum_lower_bound {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ^ 2 ≤ 2) :
    Real.sqrt 2 ≤ t + Real.sqrt (2 - t ^ 2) := by
  have hsq :
      (Real.sqrt 2) ^ 2 ≤ (t + Real.sqrt (2 - t ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ 2 - t ^ 2), ht0,
      Real.sqrt_nonneg (2 - t ^ 2)]
  have hleft_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hright_nonneg : 0 ≤ t + Real.sqrt (2 - t ^ 2) := by positivity
  rw [sq_le_sq, abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at hsq
  exact hsq

lemma max_response_sq {t : ℝ} (ht : t ^ 2 ≤ 2) :
    (Real.sqrt (2 - t ^ 2)) ^ 2 = 2 - t ^ 2 := by
  rw [Real.sq_sqrt (by linarith)]

lemma exists_alice_forced_loss_time {c : ℝ} (hc : c < threshold) :
    ∃ k : ℕ, c * (2 * (k : ℝ) + 1) - Real.sqrt 2 * (k : ℝ) < 0 := by
  let a : ℝ := Real.sqrt 2 - 2 * c
  have ha : 0 < a := by
    dsimp [a]
    rw [← two_mul_threshold]
    nlinarith
  obtain ⟨k, hk⟩ := exists_nat_gt (c / a)
  use k
  have hmul := mul_lt_mul_of_pos_right hk ha
  field_simp [ne_of_gt ha] at hmul
  dsimp [a] at hmul
  nlinarith

lemma play_one_even_zero {s : Strategy} {n : ℕ} {i : Fin n} (hi_even : Even (i : ℕ)) :
    s.play 1 (fun _ ↦ 0) n i = 0 := by
  have hlt : (i : ℕ) < n := i.isLt
  rw [Strategy.play_apply_eq_step (s := s) (p := 1)
    (opponentMoves := fun _ ↦ 0) hlt]
  have hmod : (i : ℕ) % 2 = 0 := Nat.even_iff.mp hi_even
  rw [Strategy.play]
  have hlast : (⟨(i : ℕ), Nat.lt_succ_self (i : ℕ)⟩ : Fin ((i : ℕ) + 1)) =
      Fin.last (i : ℕ) := by
    ext
    simp
  rw [hlast]
  simp [hmod]

lemma play_one_zero_even_step_valid {c : ℝ} (hc : threshold ≤ c) (s : Strategy) {m : ℕ}
    (hmeven : Even m) (hprev : ValidSeq c (s.play 1 (fun _ ↦ 0) m)) :
    ValidSeq c (s.play 1 (fun _ ↦ 0) (m + 1)) := by
  obtain ⟨r, hm_eq⟩ : ∃ r, m = 2 * r := by
    rcases hmeven with ⟨r, hr⟩
    exact ⟨r, by simpa [two_mul] using hr⟩
  subst m
  rw [Strategy.play]
  simp only [Nat.mul_mod_right, zero_ne_one, ↓reduceIte]
  refine ValidSeq.snoc hprev (by norm_num) ?_ ?_
  · intro _heven
    have hzero : ∀ i : Fin (2 * r), Even (i : ℕ) →
        s.play 1 (fun _ ↦ 0) (2 * r) i = 0 := fun i hi => play_one_even_zero hi
    have hsum_le := valid_even_zero_sum_le hprev hzero
    have hlin := sqrt_two_mul_le_c_mul_odd hc r
    norm_num [Nat.cast_mul]
    nlinarith [hsum_le, hlin]
  · intro hodd
    exfalso
    exact Nat.not_even_iff_odd.mpr hodd (even_two_mul r)

lemma bazzaMax_play_two_mul_add_two (opponentMoves : ℕ → ℝ) (r : ℕ) :
    BazzaMaxStrategy.play 1 opponentMoves (2 * r + 2) =
      Fin.snoc (Fin.snoc (BazzaMaxStrategy.play 1 opponentMoves (2 * r))
        (opponentMoves (2 * r)))
        (Real.sqrt (2 - (opponentMoves (2 * r)) ^ 2)) := by
  simp [Strategy.play, BazzaMaxStrategy, Nat.mul_mod_right, Nat.add_mod, Fin.snoc]

lemma bazzaMax_play_two_mul_add_one (opponentMoves : ℕ → ℝ) (r : ℕ) :
    BazzaMaxStrategy.play 1 opponentMoves (2 * r + 1) =
      Fin.snoc (BazzaMaxStrategy.play 1 opponentMoves (2 * r)) (opponentMoves (2 * r)) := by
  simp [Strategy.play, Nat.mul_mod_right]

lemma sum_snoc_snoc {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) :
    (∑ i : Fin (n + 2), (Fin.snoc (Fin.snoc x a) b) i) =
      (∑ i : Fin n, x i) + a + b := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp

lemma sum_sq_snoc_snoc {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) :
    (∑ i : Fin (n + 2), (Fin.snoc (Fin.snoc x a) b) i ^ 2) =
      (∑ i : Fin n, x i ^ 2) + a ^ 2 + b ^ 2 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp

lemma sum_snoc {n : ℕ} (x : Fin n → ℝ) (a : ℝ) :
    (∑ i : Fin (n + 1), (Fin.snoc x a) i) = (∑ i : Fin n, x i) + a := by
  rw [Fin.sum_univ_castSucc]; simp

lemma sum_sq_snoc {n : ℕ} (x : Fin n → ℝ) (a : ℝ) :
    (∑ i : Fin (n + 1), (Fin.snoc x a) i ^ 2) = (∑ i : Fin n, x i ^ 2) + a ^ 2 := by
  rw [Fin.sum_univ_castSucc]; simp

lemma valid_snoc_even_last {c : ℝ} {r : ℕ} {x : Fin (2 * r) → ℝ} {t : ℝ}
    (hvalid : ValidSeq c (Fin.snoc x t)) :
    0 ≤ t ∧ (∑ i, x i) + t ≤ c * (2 * (r : ℝ) + 1) := by
  constructor
  · simpa using hvalid.1 (Fin.last (2 * r))
  · have hlin := hvalid.2.1 (Fin.last (2 * r))
      (by change Even (2 * r); exact even_two_mul r)
    change (∑ j ≤ (⊤ : Fin (2 * r + 1)), (Fin.snoc x t) j) ≤
      c * (((2 * r : ℕ) : ℝ) + 1) at hlin
    rw [Finset.Iic_top] at hlin
    simpa [sum_snoc, Nat.cast_mul] using hlin

lemma valid_snoc_even_last_sq_le {c : ℝ} {r : ℕ} {x : Fin (2 * r) → ℝ} {t : ℝ}
    (hc : c ≤ threshold) (hvalid : ValidSeq c (Fin.snoc x t))
    (hsum_ge : Real.sqrt 2 * (r : ℝ) ≤ ∑ i, x i) :
    0 ≤ t ∧ t ^ 2 ≤ 2 := by
  obtain ⟨ht0, hlin⟩ := valid_snoc_even_last hvalid
  have ht_le_threshold : t ≤ threshold := by
    have hc_bound : c * (2 * (r : ℝ) + 1) ≤ threshold * (2 * (r : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    rw [threshold_mul_odd] at hc_bound
    nlinarith
  refine ⟨ht0, ?_⟩
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ)), ht0,
    le_trans ht_le_threshold threshold_le_sqrt_two, Real.sqrt_nonneg 2]

-- Each completed Alice/Bazza pair has square-sum exactly `2` and sum at least `sqrt 2`.
lemma bazzaMax_full_pairs_sum_sq {c : ℝ} (hc : c ≤ threshold)
    (opponentMoves : ℕ → ℝ) :
    ∀ r : ℕ, ValidSeq c (BazzaMaxStrategy.play 1 opponentMoves (2 * r)) →
      Real.sqrt 2 * (r : ℝ) ≤ ∑ i, BazzaMaxStrategy.play 1 opponentMoves (2 * r) i ∧
      (∑ i, (BazzaMaxStrategy.play 1 opponentMoves (2 * r) i) ^ 2) = 2 * (r : ℝ) := by
  intro r
  induction r with
  | zero =>
      intro _hvalid
      constructor <;> simp [Strategy.play]
  | succ r ih =>
      rw [show 2 * Nat.succ r = 2 * r + 2 by
        rw [Nat.mul_succ]]
      intro hvalid
      let x : Fin (2 * r) → ℝ := BazzaMaxStrategy.play 1 opponentMoves (2 * r)
      let t : ℝ := opponentMoves (2 * r)
      let b : ℝ := Real.sqrt (2 - t ^ 2)
      have hplay : BazzaMaxStrategy.play 1 opponentMoves (2 * r + 2) =
          Fin.snoc (Fin.snoc x t) b := by
        dsimp [x, t, b]
        exact bazzaMax_play_two_mul_add_two opponentMoves r
      rw [hplay] at hvalid ⊢
      have hvalid_y : ValidSeq c (Fin.snoc x t) := ValidSeq.init hvalid
      have hvalid_x : ValidSeq c x := ValidSeq.init hvalid_y
      have hih := ih (by simpa [x] using hvalid_x)
      have hsum_ge : Real.sqrt 2 * (r : ℝ) ≤ ∑ i, x i := by
        simpa [x] using hih.1
      have hsq_eq : (∑ i, x i ^ 2) = 2 * (r : ℝ) := by
        simpa [x] using hih.2
      obtain ⟨ht0, ht_sq_le⟩ := valid_snoc_even_last_sq_le hc hvalid_y hsum_ge
      have hb_sq : b ^ 2 = 2 - t ^ 2 := by simpa [b] using max_response_sq ht_sq_le
      have hpair : Real.sqrt 2 ≤ t + b := by
        simpa [b] using pair_sum_lower_bound ht0 ht_sq_le
      constructor
      · have hsum_full := sum_snoc_snoc x t b
        rw [hsum_full]
        norm_num
        nlinarith [hsum_ge, hpair]
      · have hsq_full := sum_sq_snoc_snoc x t b
        norm_num
        nlinarith [hsq_full, hsq_eq, hb_sq]

lemma bazzaMax_odd_step_valid {c : ℝ} (hc : c ≤ threshold)
    (opponentMoves : ℕ → ℝ) {m : ℕ} (hmodd : Odd m)
    (hprev : ValidSeq c (BazzaMaxStrategy.play 1 opponentMoves m)) :
    ValidSeq c (BazzaMaxStrategy.play 1 opponentMoves (m + 1)) := by
  obtain ⟨r, hm_eq⟩ : ∃ r, m = 2 * r + 1 := by
    rcases hmodd with ⟨r, hr⟩
    exact ⟨r, by simpa [two_mul, Nat.add_assoc] using hr⟩
  subst m
  let x : Fin (2 * r) → ℝ := BazzaMaxStrategy.play 1 opponentMoves (2 * r)
  let t : ℝ := opponentMoves (2 * r)
  let b : ℝ := Real.sqrt (2 - t ^ 2)
  have hprev_play : BazzaMaxStrategy.play 1 opponentMoves (2 * r + 1) = Fin.snoc x t := by
    dsimp [x, t]
    exact bazzaMax_play_two_mul_add_one opponentMoves r
  rw [hprev_play] at hprev
  have hvalid_x : ValidSeq c x := ValidSeq.init hprev
  have hfull := bazzaMax_full_pairs_sum_sq hc opponentMoves r (by simpa [x] using hvalid_x)
  have hsum_ge : Real.sqrt 2 * (r : ℝ) ≤ ∑ i, x i := by
    simpa [x] using hfull.1
  have hsq_eq : (∑ i, x i ^ 2) = 2 * (r : ℝ) := by
    simpa [x] using hfull.2
  obtain ⟨_ht0, ht_sq_le⟩ := valid_snoc_even_last_sq_le hc hprev hsum_ge
  have hb_sq : b ^ 2 = 2 - t ^ 2 := by simpa [b] using max_response_sq ht_sq_le
  change ValidSeq c (BazzaMaxStrategy.play 1 opponentMoves (2 * r + 2))
  have hnext_play : BazzaMaxStrategy.play 1 opponentMoves (2 * r + 2) =
      Fin.snoc (Fin.snoc x t) b := by
    dsimp [x, t, b]
    exact bazzaMax_play_two_mul_add_two opponentMoves r
  rw [hnext_play]
  refine ValidSeq.snoc hprev (by dsimp [b]; positivity) ?_ ?_
  · intro heven
    exfalso
    exact Nat.not_even_iff_odd.mpr (by use r) heven
  · intro _hodd
    have hsq_prev := sum_sq_snoc x t
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith [hsq_prev, hsq_eq, hb_sq]

lemma bazzaMax_forced_alice_invalid {c : ℝ} (hc : c ≤ threshold)
    (opponentMoves : ℕ → ℝ) {k : ℕ}
    (hgap : c * (2 * (k : ℝ) + 1) - Real.sqrt 2 * (k : ℝ) < 0) :
    ¬ ValidSeq c (BazzaMaxStrategy.play 1 opponentMoves (2 * k + 1)) := by
  intro hvalid
  let x : Fin (2 * k) → ℝ := BazzaMaxStrategy.play 1 opponentMoves (2 * k)
  let t : ℝ := opponentMoves (2 * k)
  have hplay : BazzaMaxStrategy.play 1 opponentMoves (2 * k + 1) = Fin.snoc x t := by
    dsimp [x, t]
    exact bazzaMax_play_two_mul_add_one opponentMoves k
  rw [hplay] at hvalid
  have hvalid_x : ValidSeq c x := ValidSeq.init hvalid
  have hfull := bazzaMax_full_pairs_sum_sq hc opponentMoves k (by simpa [x] using hvalid_x)
  have hsum_ge : Real.sqrt 2 * (k : ℝ) ≤ ∑ i, x i := by
    simpa [x] using hfull.1
  obtain ⟨ht0, hlin⟩ := valid_snoc_even_last hvalid
  nlinarith

lemma bazzaMaxStrategy_winning_of_lt_threshold {c : ℝ} (hc : c < threshold) :
    BazzaMaxStrategy.Winning c 1 := by
  intro opponentMoves
  obtain ⟨k, hk⟩ := exists_alice_forced_loss_time hc
  refine ⟨2 * k + 1, Strategy.wins_of_forced_invalid BazzaMaxStrategy c 1
    opponentMoves ?_ ?_⟩
  · simpa using bazzaMax_forced_alice_invalid (c := c) (le_of_lt hc) opponentMoves hk
  · intro m _hmle hmparity hprev
    exact bazzaMax_odd_step_valid (c := c) (le_of_lt hc) opponentMoves
      (Nat.odd_iff.mpr hmparity) hprev

lemma bazza_winning_of_lt_threshold {c : ℝ} (hc : c < threshold) :
    ∃ s : Strategy, s.Winning c 1 := by
  exact ⟨BazzaMaxStrategy, bazzaMaxStrategy_winning_of_lt_threshold hc⟩

lemma bazzaMax_no_alice_win_of_le_threshold {c : ℝ} (hc : c ≤ threshold)
    (opponentMoves : ℕ → ℝ) :
    ∀ k : ℕ, ¬ Wins c 0 (BazzaMaxStrategy.play 1 opponentMoves k) := by
  intro k hwin
  rcases hwin with ⟨i, hi_parity, hleast⟩
  have hi_mod_one : (i : ℕ) % 2 = 1 :=
    Nat.not_even_iff.mp (by simpa [Nat.even_iff] using hi_parity)
  have hi_odd : Odd (i : ℕ) := Nat.odd_iff.mpr hi_mod_one
  have hprev_valid :=
    Strategy.valid_before_first_bad BazzaMaxStrategy 1 opponentMoves hleast
  have hnext_valid := bazzaMax_odd_step_valid hc opponentMoves hi_odd hprev_valid
  exact (Strategy.invalid_at_first_bad BazzaMaxStrategy 1 opponentMoves hleast) hnext_valid

-- Replay an arbitrary Alice strategy against Bazza's maximal responses.
noncomputable def AliceVsBazzaMaxPlay (s : Strategy) : (k : ℕ) → Fin k → ℝ
| 0 => Fin.elim0
| k + 1 => Fin.snoc (AliceVsBazzaMaxPlay s k)
    (if k % 2 = 0 then s (AliceVsBazzaMaxPlay s k)
      else BazzaMaxStrategy (AliceVsBazzaMaxPlay s k))

noncomputable def AliceMovesAgainstBazzaMax (s : Strategy) : ℕ → ℝ :=
  fun k => if k % 2 = 0 then s (AliceVsBazzaMaxPlay s k) else 0

noncomputable def BazzaMaxCounterplay (s : Strategy) : ℕ → ℝ :=
  fun k => if k % 2 = 1 then BazzaMaxStrategy (AliceVsBazzaMaxPlay s k) else 0

lemma strategy_play_bazzaMaxCounterplay (s : Strategy) :
    ∀ k : ℕ, s.play 0 (BazzaMaxCounterplay s) k = AliceVsBazzaMaxPlay s k := by
  intro k
  induction k with
  | zero =>
      simp [Strategy.play, AliceVsBazzaMaxPlay]
  | succ k ih =>
      rw [Strategy.play, AliceVsBazzaMaxPlay, ih]
      by_cases h0 : k % 2 = 0
      · simp [h0]
      · have h1 : k % 2 = 1 :=
          Nat.not_even_iff.mp (by simpa [Nat.even_iff] using h0)
        simp [BazzaMaxCounterplay, h1]

lemma aliceVsBazzaMaxPlay_eq_bazzaMax_play (s : Strategy) :
    ∀ k : ℕ,
      AliceVsBazzaMaxPlay s k =
        BazzaMaxStrategy.play 1 (AliceMovesAgainstBazzaMax s) k := by
  intro k
  induction k with
  | zero =>
      simp [Strategy.play, AliceVsBazzaMaxPlay]
  | succ k ih =>
      rw [AliceVsBazzaMaxPlay, Strategy.play, ← ih]
      by_cases h0 : k % 2 = 0
      · simp [AliceMovesAgainstBazzaMax, h0]
      · have h1 : k % 2 = 1 :=
          Nat.not_even_iff.mp (by simpa [Nat.even_iff] using h0)
        simp [h1]

lemma alice_zero_counterplay_of_threshold_le {c : ℝ} (hc : threshold ≤ c) (s : Strategy) :
    ∃ opponentMoves : ℕ → ℝ, ∀ k : ℕ, ¬ Wins c 1 (s.play 1 opponentMoves k) := by
  use fun _ ↦ 0
  intro k hwin
  rcases hwin with ⟨i, hi_parity, hleast⟩
  have hi_mod_zero : (i : ℕ) % 2 = 0 :=
    Nat.not_odd_iff.mp (by simpa [Nat.odd_iff] using hi_parity)
  have hi_even : Even (i : ℕ) := Nat.even_iff.mpr hi_mod_zero
  have hprev_valid :=
    Strategy.valid_before_first_bad s 1 (fun _ ↦ 0) hleast
  have hnext_valid := play_one_zero_even_step_valid hc s hi_even hprev_valid
  exact (Strategy.invalid_at_first_bad s 1 (fun _ ↦ 0) hleast) hnext_valid

lemma bazza_max_counterplay_of_le_threshold {c : ℝ} (hc : c ≤ threshold) (s : Strategy) :
    ∃ opponentMoves : ℕ → ℝ, ∀ k : ℕ, ¬ Wins c 0 (s.play 0 opponentMoves k) := by
  use BazzaMaxCounterplay s
  intro k hwin
  have hplay :
      s.play 0 (BazzaMaxCounterplay s) k =
        BazzaMaxStrategy.play 1 (AliceMovesAgainstBazzaMax s) k := by
    rw [strategy_play_bazzaMaxCounterplay, aliceVsBazzaMaxPlay_eq_bazzaMax_play]
  rw [hplay] at hwin
  exact bazzaMax_no_alice_win_of_le_threshold hc (AliceMovesAgainstBazzaMax s) k hwin

lemma not_bazza_winning_of_threshold_le {c : ℝ} (hc : threshold ≤ c) :
    ¬ ∃ s : Strategy, s.Winning c 1 := by
  rintro ⟨s, hs⟩
  obtain ⟨opponentMoves, hcounter⟩ := alice_zero_counterplay_of_threshold_le hc s
  obtain ⟨k, hk⟩ := hs opponentMoves
  exact hcounter k hk

lemma not_alice_winning_of_le_threshold {c : ℝ} (hc : c ≤ threshold) :
    ¬ ∃ s : Strategy, s.Winning c 0 := by
  rintro ⟨s, hs⟩
  obtain ⟨opponentMoves, hcounter⟩ := bazza_max_counterplay_of_le_threshold hc s
  obtain ⟨k, hk⟩ := hs opponentMoves
  exact hcounter k hk

lemma alice_winning_iff {c : ℝ} :
    (∃ s : Strategy, s.Winning c 0) ↔ threshold < c := by
  constructor
  · intro hs
    by_contra hlt
    exact not_alice_winning_of_le_threshold (le_of_not_gt hlt) hs
  · intro hc
    exact alice_winning_of_threshold_lt hc

lemma bazza_winning_iff {c : ℝ} :
    (∃ s : Strategy, s.Winning c 1) ↔ c < threshold := by
  constructor
  · intro hs
    by_contra hlt
    exact not_bazza_winning_of_threshold_le (le_of_not_gt hlt) hs
  · intro hc
    exact bazza_winning_of_lt_threshold hc

snip end

/-- The answer to be determined. -/
noncomputable determine answer : Set ℝ × Set ℝ :=
  ({c : ℝ | threshold < c}, {c : ℝ | c < threshold})

problem imo2025_p5 :
    ({c : ℝ | ∃ s : Strategy, s.Winning c 0},
      {c : ℝ | ∃ s : Strategy, s.Winning c 1}) =
      answer := by
  change
    ({c : ℝ | ∃ s : Strategy, s.Winning c 0},
      {c : ℝ | ∃ s : Strategy, s.Winning c 1}) =
      ({c : ℝ | threshold < c}, {c : ℝ | c < threshold})
  apply Prod.ext
  · ext c
    simpa using (alice_winning_iff (c := c))
  · ext c
    simpa using (bazza_winning_iff (c := c))

end Imo2025P5
