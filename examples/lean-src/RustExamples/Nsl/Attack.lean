module

public import RustExamples.Nsl.Refine

/-! # Lowe's attack on Needham–Schroeder

`lowe_attack` shows that the adversary `LoweAttack` wins the real secrecy game
against the original protocol (`lowe = false`) with three queries, for every
correct encryption scheme, all total tapes and all coins.

The proof rewrites the extracted game into the pure model `pgame` over
`realEnv` (`real_game`) and evaluates the three rounds with `simp`. The only
facts beyond computation are that decryption inverts encryption (`dec_enc`,
from `Pke.Correct`) and that the adversary reads B's public key at index 2
(`index_two`).
-/

open Aeneas Aeneas.Std Result

namespace examples.nsl

open Model

namespace Attack

variable {P Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}

/-- Decrypting with the secret key of seed `s` inverts encrypting to its public key. -/
theorem dec_enc (hE : E.Correct) (s : Seed) (m : Msg Std.U64) (r : Coins) :
    (pkeF hE.toTotal).dec ((pkeF hE.toTotal).keygen s).2
      ((pkeF hE.toTotal).enc ((pkeF hE.toTotal).keygen s).1 m r) = some m := by
  have := hE.dec_enc s _ _ m r _ (keygen_eq hE.toTotal s) (enc_eq hE.toTotal _ m r)
  rw [dec_eq hE.toTotal] at this
  simpa using this

/-- Casting agent B's name to an index gives 2. -/
theorem cast_two : UScalar.cast .Usize 2#u8 = 2#usize := by
  apply UScalar.eq_of_val_eq; simp

/-- Index 2 of the public keys is B's key from the oracle tape. -/
theorem index_two (F : PkeF Seed Coins Pk Sk Ct) (t u : TapeF Seed Coins) :
    (keysVec F t u).index_usize 2#usize = ok (F.keygen (u.seed 2#u8)).1 := by
  simp [keysVec, publicKeys, alloc.vec.Vec.index_usize]
  rfl

end Attack

open Attack

/-- **Lowe's attack on Needham–Schroeder.** Without Lowe's check (`lowe = false`),
`LoweAttack` wins the real secrecy game with three queries, for every correct
encryption scheme `E`, all total tapes and all randomness: the game returns
`ok (true, _)`.

The run: A (agent 1) starts session 0 with the adversary (agent 0). The
adversary decrypts A's message one and re-encrypts it to B (agent 2), who opens
responder session 1 with peer A and replies to A. The adversary forwards the
reply to session 0, which accepts it and sends B's nonce to the adversary, who
names session 1 and that nonce. -/
public theorem lowe_attack {P Seed Coins Pk Sk Ct T U : Type _} {E : Pke P Seed Coins Pk Sk Ct}
    (hE : E.Correct) {TI : Tape T Seed Coins} {UI : Tape U Seed Coins} (hT : TI.Total)
    (hU : UI.Total) (tape : T) (oracle_tape : U) (coins : Coins) :
    ∃ adv, (do
      let o ← RealOracle.new E UI oracle_tape
      let a ← LoweAttack.new E coins
      secrecy_game E TI (RealOracle.Insts.ExamplesNslOracle E UI)
        (LoweAttack.Insts.ExamplesNslAdversary E) false tape o a 3#usize) = ok (true, adv) := by
  simp only [RealOracle.new, LoweAttack.new, bind_ok, real_game hE.toTotal hT hU]
  simp [pgame, pplay, pstep, realEnv, LoweAttack.Insts.ExamplesNslAdversary.start,
    LoweAttack.Insts.ExamplesNslAdversary.next, LoweAttack.Insts.ExamplesNslAdversary.guess,
    LoweAttack.decrypt, dec_eq hE.toTotal, enc_eq hE.toTotal, PkeF.encTo, PkeF.decBy,
    dec_enc hE, A, B, ADVERSARY, cast_two, index_two, wins, lift]

end examples.nsl
