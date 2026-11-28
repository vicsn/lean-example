module

public import RustExamples.Gen.Funs

/-! Assumptions about the `Pke` and `Tape` implementations that the NSL proofs
rely on.

The Rust trait methods become fields of `nsl.Pke` and `nsl.Tape`, each returning
a `Result`. The deterministic theorems need only that these never fail and that
`==` on ciphertexts decides equality. Nothing here is a security assumption:
the security of the encryption enters only as the IND-CCA advantage in the
final bound.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace examples.nsl

open Classical in
/-- A `Pke` whose functions never fail and whose ciphertext equality is real
equality. -/
structure Pke.Total {P Seed Coins Pk Sk Ct : Type _} (E : Pke P Seed Coins Pk Sk Ct) :
    Prop where
  keygen_ok : ∀ s, ∃ k, E.keygen s = ok k
  enc_ok : ∀ pk m r, ∃ c, E.enc pk m r = ok c
  dec_ok : ∀ sk c, ∃ m, E.dec sk c = ok m
  eq_ok : ∀ a b : Ct, E.corecmpEqInst.partialEqInst.eq a b = ok (decide (a = b))

/-- A total `Pke` for which decrypting with the matching secret key gives
the message back. Only Lowe's attack needs this. -/
structure Pke.Correct {P Seed Coins Pk Sk Ct : Type _} (E : Pke P Seed Coins Pk Sk Ct) :
    Prop extends E.Total where
  dec_enc : ∀ s pk sk m r c,
    E.keygen s = ok (pk, sk) → E.enc pk m r = ok c → E.dec sk c = ok (some m)

/-- A `Tape` whose functions never fail. -/
structure Tape.Total {T Seed Coins : Type _} (I : Tape T Seed Coins) : Prop where
  seed_ok : ∀ t a, ∃ s, I.seed t a = ok s
  coins_ok : ∀ t i, ∃ r, I.coins t i = ok r
  nonce_ok : ∀ t k, ∃ n, I.nonce t k = ok n

end examples.nsl

