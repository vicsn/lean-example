//! Symbolic client authentication for signed Merkle roots in the "MerkleTree PKI".
//! Trace positions count all entries, including network and private state.
//! The network can replay messages and construct terms from anything it knows.
//! Hashes and signatures are symbolic constructors. Only concatenations can
//! be split. Fresh values are identified by their position in the trace.
//!
//! The audit starts with `client_authentication`, `check_history`, and `classify`
//! below. The proof interprets the Rust programs in `roles.rs` with dylean's
//! symbolic primitives. `native.rs` implements the primitives for Cargo runs.
//! Hash-node tags separate empty trees, leaves, and internal nodes. A server
//! signs the root together with the leaf count under its registered key.
//!
//! Symbolic byte strings compare by constructor and contents. Hashes and
//! verification keys are unary constructors. Signatures contain a signing key,
//! fresh nonce and message. Verification checks the message and the public key
//! derived from the signing key. The attacker can build these terms only from
//! values it knows. Receiving a network handle reveals its message, while
//! private keys and stored element lists require their own typed state handles.
//! A compromise publishes that state and records the owner before publication.

#[cfg(not(hax))]
mod native;
mod roles;
#[cfg(not(hax))]
pub use native::{Bytes, Entry, Server, check, observe, run};
pub use roles::Recipe;

/// Observations of one server and element at a single trace position.
/// Every entry, including an unrelated one, occupies one position.
#[derive(Clone, Copy)]
pub enum Observation {
    Other,
    Authenticated,
    KeyCompromised,
    Accepted,
}

/// Protocol events at a single trace position, compared with the query's
/// server and element. Key compromise is looked up in the MerkleTree PKI.
enum Event {
    Other,
    ServerAuthenticated {
        same_server: bool,
        same_element: bool,
    },
    ClientAccept {
        same_server: bool,
        same_element: bool,
    },
}

fn classify(event: Event, server_key_compromised: bool) -> Observation {
    if server_key_compromised {
        return Observation::KeyCompromised;
    }
    match event {
        Event::ServerAuthenticated {
            same_server: true,
            same_element: true,
        } => Observation::Authenticated,
        Event::ClientAccept {
            same_server: true,
            same_element: true,
        } => Observation::Accepted,
        _ => Observation::Other,
    }
}

/// A view of an execution for a specified server and element.
/// Positions beyond the end of the trace yield Other.
trait History<S, B> {
    fn at(&self, server: &S, element: &B, time: usize) -> Observation;
}

/// If the client accepts at time t, the same server previously authenticated
/// this element or one of that server's MerkleTree PKI keys was compromised.
fn check_history<H: History<S, B>, S, B>(
    history: &H,
    server: &S,
    element: &B,
    time: usize,
) -> bool {
    if !matches!(history.at(server, element, time), Observation::Accepted) {
        return true;
    }
    let mut i = time;
    while i > 0 {
        i -= 1;
        match history.at(server, element, i) {
            Observation::Authenticated | Observation::KeyCompromised => return true,
            _ => {}
        }
    }
    false
}

/// Handles name entries by their absolute position. Actions may be repeated
/// and interleaved for arbitrary servers and independently generated keys.
pub enum Action<S> {
    /// Evaluate an attacker recipe and publish its result on success.
    Send(Recipe),
    /// Generate fresh bytes of the requested length and publish them.
    Random(usize),
    /// Generate a fresh 32-byte signing key, publish its verification key,
    /// and register the public and private key entries for this server.
    GenerateKey(S),
    /// Log compromise of the stored private key and publish the leaked state.
    CompromiseKey(usize),
    /// Log compromise of an element list and publish it.
    CompromiseState(usize),
    Authenticate {
        server: S,
        messages: Vec<usize>,
        key: usize,
    },
    ProveInclusion {
        server: S,
        state: usize,
        index: usize,
    },
    CheckInclusion {
        server: S,
        signed_root: usize,
        opening: usize,
        key: usize,
    },
}

/// Operations of the MerkleTree PKI symbolic trace. Failed operations retain
/// entries already produced. Only the runner can choose which operation runs.
trait Execution<S, B>: History<S, B> + Sized {
    fn empty() -> Self;
    fn send(&mut self, recipe: &Recipe);
    fn random(&mut self, len: usize);
    fn generate_key(&mut self, server: &S);
    fn compromise_key(&mut self, key: usize);
    fn compromise_state(&mut self, state: usize);
    fn authenticate(&mut self, server: &S, messages: &[usize], key: usize);
    fn prove_inclusion(&mut self, server: &S, state: usize, index: usize);
    fn check_inclusion(&mut self, server: &S, signed_root: usize, opening: usize, key: usize);
}

fn execute<W: Execution<S, B>, S, B>(actions: &[Action<S>]) -> W {
    let mut trace = W::empty();
    let mut i = 0;
    while i < actions.len() {
        match &actions[i] {
            Action::Send(r) => trace.send(r),
            Action::Random(n) => trace.random(*n),
            Action::GenerateKey(s) => trace.generate_key(s),
            Action::CompromiseKey(h) => trace.compromise_key(*h),
            Action::CompromiseState(h) => trace.compromise_state(*h),
            Action::Authenticate {
                server,
                messages,
                key,
            } => trace.authenticate(server, messages, *key),
            Action::ProveInclusion {
                server,
                state,
                index,
            } => trace.prove_inclusion(server, *state, *index),
            Action::CheckInclusion {
                server,
                signed_root,
                opening,
                key,
            } => trace.check_inclusion(server, *signed_root, *opening, *key),
        }
        i += 1;
    }
    trace
}

/// On execution from the empty trace, every acceptance of this element for
/// this server has a matching authentication or a prior compromise of any
/// long-term signing key of this server in the MerkleTree PKI. The proved
/// instance of `Execution` runs the Rust roles with dylean's symbolic
/// primitives. `check` runs the same roles with the native interpreter.
#[cfg_attr(hax, hax_lib::ensures(|result| result))]
fn client_authentication<W: Execution<S, B>, S, B>(
    actions: &[Action<S>],
    server: &S,
    element: &B,
    time: usize,
) -> bool {
    let trace = execute::<W, S, B>(actions);
    check_history(&trace, server, element, time)
}
