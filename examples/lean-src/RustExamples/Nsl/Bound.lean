module

public import RustExamples.Nsl.Probability
import RustExamples.Nsl.Refine
import RustExamples.Nsl.Ideal

/-! # The concrete security bound for NSL secrecy

For every total `Pke` with finite `Seed` and `Coins`, every adversary (any
`Adversary` instance with any initial state) and every number of queries `q`,
with both tapes uniform (see `RustExamples.Nsl.Probability`):

1. **Real → ideal** (`game_hop`). The real and the ideal secrecy games are the
   reduction `reduction E Adv adv lowe q` (the secrecy game with the oracle
   left abstract) run with `RealOracle` and with `IdealOracle`. Their winning
   probabilities differ by exactly the multi-user IND-CCA advantage of that
   reduction.
2. **Ideal** (`idealWin_le`, in `RustExamples.Nsl.Ideal`). With Lowe's check, the
   adversary wins the ideal game with probability at most `q (q + 1) / 2^64`.

`secrecy_bound` adds them up.
-/

open Aeneas Aeneas.Std Result

namespace examples.nsl.Game

variable {P Seed Coins Pk Sk Ct A : Type} [Fintype Seed] [Fintype Coins]

/-- A game returning `(b, _)` outputs `true` exactly when `b` is `true`. -/
theorem fst_eq_ok_true {X : Type} (m : Result (Bool × X)) :
    (do let (b, _) ← m; ok b) = ok true ↔ ∃ x, m = ok (true, x) := by
  constructor
  · intro h
    obtain ⟨⟨b, x⟩, hm, hb⟩ := bind_eq_ok h
    simp only [uncurry_apply_pair, Result.ok.injEq] at hb
    exact ⟨x, by rw [hm, hb]⟩
  · rintro ⟨x, hm⟩
    simp [hm]

/-- The real game is the reduction run with the real oracle. -/
theorem realWin_eq (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (q : Std.Usize) :
    realWin E Adv adv lowe q = ccaReal E q.val (reduction E Adv adv lowe q) := by
  unfold realWin ccaReal reduction
  congr 1
  funext ω
  simp only [RealOracle.new, bind_ok]
  exact propext (fst_eq_ok_true _).symm

/-- The ideal game is the reduction run with the ideal oracle. -/
theorem idealWin_eq (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (q : Std.Usize) :
    idealWin E Adv adv lowe q = ccaIdeal E q.val (reduction E Adv adv lowe q) := by
  unfold idealWin ccaIdeal reduction
  congr 1
  funext ω
  simp only [IdealOracle.new, RealOracle.new, bind_ok]
  exact propext (fst_eq_ok_true _).symm

/-- **The IND-CCA hop.** The real and ideal secrecy games differ by exactly
the multi-user IND-CCA advantage of the reduction. -/
public theorem game_hop (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (q : Std.Usize) :
    |realWin E Adv adv lowe q - idealWin E Adv adv lowe q| =
      advCCA E q.val (reduction E Adv adv lowe q) := by
  rw [realWin_eq, idealWin_eq]; rfl

/-- **Secrecy of NSL.** The adversary wins the real secrecy game (with Lowe's
check) with probability at most the multi-user IND-CCA advantage of the
reduction plus `q (q + 1) / 2^64`. -/
public theorem secrecy_bound {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total)
    (Adv : Adversary A Pk Sk Ct) (adv : A) (q : Std.Usize) :
    realWin E Adv adv true q ≤
      advCCA E q.val (reduction E Adv adv true q) + (q.val * (q.val + 1) : ℝ) / 2 ^ 64 := by
  have h1 := game_hop E Adv adv true q
  have h2 := idealWin_le hE Adv adv q
  have h3 := le_abs_self (realWin E Adv adv true q - idealWin E Adv adv true q)
  linarith

end examples.nsl.Game
