module

public import RustExamples.Nsl.Lawful
public import RustExamples.Nsl.Probability
import RustExamples.Nsl.Secrecy
import RustExamples.Nsl.Faithful
import RustExamples.Nsl.Attack
import RustExamples.Nsl.Ideal
import RustExamples.Nsl.Bound

/-! # What is proved about Needham–Schroeder–Lowe

This module is the audit surface for `examples/src/nsl.rs`: it states every
theorem we prove about it, and it is the only NSL proof module that `Examples`
exports. The proofs live in `RustExamples.Nsl.*`, imported privately.

To audit, read:
* `examples/src/nsl.rs`: the protocol (`step`), the three worlds (`World` over
  `RealOracle` or `IdealOracle`, and `Symbolic`), the property functions
  `secrecy` and `faithful`, the game `secrecy_game` and the adversary
  `LoweAttack`, whose Aeneas translations in `RustExamples.Gen.Funs` the theorems
  below are about;
* `RustExamples.Nsl.Lawful`: the only assumptions on the encryption and the tapes
  (the functions never fail, ciphertext `==` is equality, and for the attack,
  decryption inverts encryption). None of them is a security assumption;
* `RustExamples.Nsl.Probability`: the definitions of the probability space
  (uniform tapes), the IND-CCA advantage and the reduction;
* the statements below.

The structure of the argument:

1. **Real → ideal** (`ind_cca_hop`). The secrecy game uses the encryption of
   honest agents only through the `Oracle` interface, so the real and ideal games
   are one program, `reduction`, run with `RealOracle` and with `IdealOracle`. Their
   winning probabilities differ by exactly its IND-CCA advantage.
2. **Ideal → symbolic** (`symbolic_secrecy`, `symbolic_faithful`). Deterministic and
   for every input, as in the Rust fuzz tests: in the symbolic world, where the
   attacked session's nonce is a symbol, Lowe's version never encrypts the
   symbol to the adversary; and the ideal world gives the adversary the same
   responses as the symbolic world unless the nonce equals one of the values
   the symbolic world compared it with.
3. **Counting** (`ideal_secrecy`). Those values do not depend on the nonce, so an
   adaptive adversary hits it with probability at most `(q + 1) / 2^64` per
   session.
4. **The bound** (`nsl_secrecy`).

The proofs do not reason about the extracted code directly.
`RustExamples.Nsl.Model` defines the protocol, the worlds and the game as pure
functions, `RustExamples.Nsl.Refine` shows that the extracted code computes them,
and the other modules are about the pure functions.

Two remarks on reading the bound. `advCCA` is the advantage in the multi-user
real-or-blank game defined in Rust (the ideal oracle encrypts a fixed message
and decrypts by table lookup); relating it to textbook IND-CCA is standard and
not formalised. And `advCCA` of an arbitrary Lean function could be large (a
non-computable function can ask which oracle type it got), but the
distinguisher in the bound is `reduction`, the extracted Rust game, which is
generic over the oracle and only calls its methods; the adversary inside it
only ever sees responses.
-/

public section

open Aeneas Aeneas.Std Result

namespace examples.nsl

/-- **Symbolic secrecy.** With Lowe's check, for every action list (every
attacker against the symbolic world, including ones that know every key and
coin on both tapes) and every attacked session index, `secrecy` returns `true`:
if the attacked session's peer is honest, no message mentioning its nonce is
ever encrypted to the adversary. This is false without the check: the Rust
fuzz test finds Lowe's attack, and `ns_lowe_attack` below shows it works. -/
theorem symbolic_secrecy {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
    {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}
    (hE : E.Total) (hT : TI.Total) (hU : UI.Total)
    (tape : T) (oracle_tape : U) (actions : Slice (Action Ct)) (secret : Std.Usize) :
    secrecy E TI UI true tape oracle_tape actions secret = ok true :=
  secrecy_holds hE hT hU tape oracle_tape actions secret

/-- **The symbolic world is faithful.** For both protocols, every action list
and attacked session `secret`, the ideal world gives the adversary the same
responses as the symbolic world on the same tapes, unless the symbolic run
leaked the symbol or compared it with the nonce that `tape` gives session
`secret`. The tape is arbitrary, so this covers every value of that nonce. -/
theorem symbolic_faithful {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
    {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}
    (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (lowe : Bool)
    (tape : T) (oracle_tape : U) (actions : Slice (Action Ct)) (secret : Std.Usize) :
    faithful E TI UI lowe tape oracle_tape actions secret = ok true :=
  faithful_holds hE hT hU lowe tape oracle_tape actions secret

/-- **Lowe's attack.** Without Lowe's check, the adversary `LoweAttack` wins the real
secrecy game with 3 queries, for every encryption scheme whose decryption
inverts encryption and for all randomness: it names B's session, whose peer
is the honest A, and outputs that session's nonce. -/
theorem ns_lowe_attack {P Seed Coins Pk Sk Ct T U : Type _} {E : Pke P Seed Coins Pk Sk Ct}
    (hE : E.Correct) {TI : Tape T Seed Coins} {UI : Tape U Seed Coins} (hT : TI.Total)
    (hU : UI.Total) (tape : T) (oracle_tape : U) (coins : Coins) :
    ∃ adv, (do
      let o ← RealOracle.new E UI oracle_tape
      let a ← LoweAttack.new E coins
      secrecy_game E TI (RealOracle.Insts.ExamplesNslOracle E UI)
        (LoweAttack.Insts.ExamplesNslAdversary E) false tape o a 3#usize) = ok (true, adv) :=
  lowe_attack hE hT hU tape oracle_tape coins

namespace Game

/-- **The IND-CCA hop.** For both protocols, every adversary (any `Adversary`
instance and initial state) and every number of queries `q`, the winning
probabilities of the real and the ideal secrecy game differ by exactly the
IND-CCA advantage of `reduction`, the secrecy game with the oracle left
abstract. -/
theorem ind_cca_hop {P Seed Coins Pk Sk Ct A : Type} [Fintype Seed] [Fintype Coins]
    (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (q : Std.Usize) :
    |realWin E Adv adv lowe q - idealWin E Adv adv lowe q| =
      advCCA E q.val (reduction E Adv adv lowe q) :=
  game_hop E Adv adv lowe q

/-- **Secrecy in the ideal game.** With Lowe's check, every adversary making `q`
queries wins the ideal secrecy game with probability at most
`q (q + 1) / 2^64`. No assumption on the encryption beyond totality: in the
ideal world honest ciphertexts carry no information. -/
theorem ideal_secrecy {P Seed Coins Pk Sk Ct A : Type} [Fintype Seed] [Fintype Coins]
    {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total)
    (Adv : Adversary A Pk Sk Ct) (adv : A) (q : Std.Usize) :
    idealWin E Adv adv true q ≤ (q.val * (q.val + 1) : ℝ) / 2 ^ 64 :=
  idealWin_le hE Adv adv q

/-- **Secrecy of NSL.** For every total encryption scheme with finite seed and
coin types, every adversary and every number of queries `q`, the probability
that the adversary names a session with an honest peer and outputs its nonce in
the real game is at most the IND-CCA advantage of `reduction` plus
`q (q + 1) / 2^64`. The bound holds for each initial state of the adversary, so
a randomised adversary is covered by averaging over its coins. -/
theorem nsl_secrecy {P Seed Coins Pk Sk Ct A : Type} [Fintype Seed] [Fintype Coins]
    {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total)
    (Adv : Adversary A Pk Sk Ct) (adv : A) (q : Std.Usize) :
    realWin E Adv adv true q ≤
      advCCA E q.val (reduction E Adv adv true q) + (q.val * (q.val + 1) : ℝ) / 2 ^ 64 :=
  secrecy_bound hE Adv adv q

end Game

end examples.nsl
