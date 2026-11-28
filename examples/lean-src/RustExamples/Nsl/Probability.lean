module

public import RustExamples.Nsl.Lawful
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic

/-! # Probability for the NSL secrecy game

A small, explicit framework:

* `GameTape Seed Coins q` is the randomness of one party of a game with `q`
  queries: a key-generation seed for each of the 256 agents, `q + 1`
  encryption coins (an index past `q` reads the last one) and a 64-bit nonce
  for each of the `q` sessions that can exist (an index past `q` reads 0).
  `gameTape` is its `Tape` instance; every nonce is an arbitrary `U64`, so under
  the uniform distribution each nonce is uniform over all 2^64 values and
  independent of everything else.
* `prob A` is the probability of the event `A` under the uniform distribution
  on a finite type: the number of outcomes in `A` divided by the number of
  outcomes.
* `advCCA E D` is the multi-user real-or-blank IND-CCA advantage of a
  distinguisher `D`: `D` gets its own tape and an oracle of an arbitrary type
  `O` implementing `Oracle` (so it can use it only through that interface),
  and the advantage is the difference between the probabilities that it
  outputs `true` with `RealOracle` and with `IdealOracle`, both built by
  `new` from the challenger's tape. Both tapes are uniform.
-/

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl.Game

/-! ## Uniform nonces -/

/-- `U64` has exactly the 2^64 values of `Fin (2 ^ 64)`. -/
def u64Equiv : Std.U64 ≃ Fin (2 ^ 64) where
  toFun u := u.bv.toFin
  invFun f := ⟨BitVec.ofFin f⟩
  left_inv u := by cases u; simp
  right_inv f := by simp

instance : Fintype Std.U64 := Fintype.ofEquiv _ u64Equiv.symm

theorem card_u64 : Fintype.card Std.U64 = 2 ^ 64 := by
  rw [Fintype.card_congr u64Equiv]; simp

/-! ## Tapes -/

/-- The randomness of one party of a game with `q` queries. -/
structure GameTape (Seed Coins : Type) (q : Nat) where
  /-- Agent `a`'s key-generation seed. -/
  seeds : Fin 256 → Seed
  /-- Encryption coins, one per encryption. -/
  coins : Fin (q + 1) → Coins
  /-- Session `k`'s nonce. -/
  nonces : Fin q → Std.U64

/-- A `GameTape` is its three tables. -/
def GameTape.equiv (Seed Coins : Type) (q : Nat) :
    GameTape Seed Coins q ≃ (Fin 256 → Seed) × (Fin (q + 1) → Coins) × (Fin q → Std.U64) where
  toFun t := (t.seeds, t.coins, t.nonces)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (Seed Coins : Type) [Fintype Seed] [Fintype Coins] (q : Nat) :
    Fintype (GameTape Seed Coins q) :=
  Fintype.ofEquiv _ (GameTape.equiv Seed Coins q).symm

/-- The `Tape` instance of `GameTape`: agent `a`'s seed is `seeds a`, the `i`-th
encryption uses `coins (min i q)`, and session `k`'s nonce is `nonces k` (0 past
`q`). -/
def gameTape (Seed Coins : Type) (q : Nat) : Tape (GameTape Seed Coins q) Seed Coins where
  seed t a := ok (t.seeds ⟨a.val, by have := a.hBounds; simp at this; omega⟩)
  coins t i := ok (t.coins ⟨min i.val q, by omega⟩)
  nonce t k := ok (if h : k.val < q then t.nonces ⟨k.val, h⟩ else 0#u64)

theorem gameTape_total (Seed Coins : Type) (q : Nat) : (gameTape Seed Coins q).Total where
  seed_ok _ _ := ⟨_, rfl⟩
  coins_ok _ _ := ⟨_, rfl⟩
  nonce_ok _ _ := ⟨_, rfl⟩

/-! ## Probability -/

open Classical in
/-- The probability of `A` when the outcome is uniform on the finite type `Ω`. -/
def prob {Ω : Type} [Fintype Ω] (A : Ω → Prop) : ℝ :=
  ((Finset.univ.filter A).card : ℝ) / Fintype.card Ω

/-! ## The multi-user IND-CCA game -/

variable {P Seed Coins Pk Sk Ct : Type} [Fintype Seed] [Fintype Coins]

/-- A distinguisher for the multi-user IND-CCA game, with its own tape of type
`T`. It must work for every oracle type `O` and gets the oracle only through the
`Oracle` interface. -/
abbrev Distinguisher (Pk Ct T : Type) := ∀ {O : Type}, Oracle O Pk Ct → T → O → Result Bool

/-- The two tapes of a game: the adversary's side (`tape`) and the
challenger's (`oracle_tape`), each uniform. -/
abbrev Outcome (Seed Coins : Type) (q : Nat) := GameTape Seed Coins q × GameTape Seed Coins q

/-- `D` outputs `true` with the real oracle built from the challenger's tape. -/
def ccaReal (E : Pke P Seed Coins Pk Sk Ct) (q : Nat)
    (D : Distinguisher Pk Ct (GameTape Seed Coins q)) : ℝ :=
  prob fun ω : Outcome Seed Coins q =>
    (do
      let o ← RealOracle.new E (gameTape Seed Coins q) ω.2
      D (RealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q)) ω.1 o) = ok true

/-- `D` outputs `true` with the ideal oracle built from the challenger's tape. -/
def ccaIdeal (E : Pke P Seed Coins Pk Sk Ct) (q : Nat)
    (D : Distinguisher Pk Ct (GameTape Seed Coins q)) : ℝ :=
  prob fun ω : Outcome Seed Coins q =>
    (do
      let o ← IdealOracle.new E (gameTape Seed Coins q) ω.2
      D (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q)) ω.1 o) = ok true

/-- The multi-user real-or-blank IND-CCA advantage of `D`. -/
def advCCA (E : Pke P Seed Coins Pk Sk Ct) (q : Nat)
    (D : Distinguisher Pk Ct (GameTape Seed Coins q)) : ℝ :=
  |ccaReal E q D - ccaIdeal E q D|

/-! ## The secrecy game -/

variable {A : Type}

/-- The reduction of the IND-CCA hop: the secrecy game run with an abstract
oracle, outputting whether the adversary won. -/
def reduction (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (q : Std.Usize) : Distinguisher Pk Ct (GameTape Seed Coins q.val) :=
  fun OI t o => do
    let (b, _) ← secrecy_game E (gameTape Seed Coins q.val) OI Adv lowe t o adv q
    ok b

/-- The probability that the adversary wins the real secrecy game. -/
def realWin (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (q : Std.Usize) : ℝ :=
  prob fun ω : Outcome Seed Coins q.val =>
    ∃ adv', (do
      let o ← RealOracle.new E (gameTape Seed Coins q.val) ω.2
      secrecy_game E (gameTape Seed Coins q.val)
        (RealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q.val)) Adv lowe ω.1 o adv q) =
      ok (true, adv')

/-- The probability that the adversary wins the ideal secrecy game. -/
def idealWin (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (q : Std.Usize) : ℝ :=
  prob fun ω : Outcome Seed Coins q.val =>
    ∃ adv', (do
      let o ← IdealOracle.new E (gameTape Seed Coins q.val) ω.2
      secrecy_game E (gameTape Seed Coins q.val)
        (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q.val)) Adv lowe ω.1 o adv q) =
      ok (true, adv')

end examples.nsl.Game
