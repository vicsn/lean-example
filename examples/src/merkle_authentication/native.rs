//! Native interpreter for the symbolic operations used by the Rust example.

use super::{History, Observation};

/// A byte string in the symbolic protocol. Concatenation preserves its boundary.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Bytes {
    Literal(Vec<u8>),
    Concat(Box<Bytes>, Box<Bytes>),
    Random {
        time: usize,
        len: usize,
    },
    Hash(Box<Bytes>),
    VerificationKey(Box<Bytes>),
    Signature {
        key: Box<Bytes>,
        nonce: Box<Bytes>,
        message: Box<Bytes>,
    },
}

impl Bytes {
    fn pair(left: Self, right: Self) -> Self {
        Self::Concat(Box::new(left), Box::new(right))
    }

    fn parts(&self) -> Option<(&Self, &Self)> {
        match self {
            Self::Concat(left, right) => Some((left, right)),
            _ => None,
        }
    }

    fn length(&self) -> Option<usize> {
        match self {
            Self::Literal(b) => Some(b.len()),
            Self::Random { len, .. } => Some(*len),
            Self::Hash(_) | Self::VerificationKey(_) => Some(32),
            Self::Signature { .. } => Some(64),
            Self::Concat(l, r) => l.length()?.checked_add(r.length()?),
        }
    }
}

// Comparse encodes a natural number as big-endian groups of 31 bits.
// Each group is a little-endian four-byte literal, followed by the suffix.
fn nat(mut n: usize, suffix: Bytes) -> Bytes {
    let mut result = Bytes::pair(
        Bytes::Literal(((n & 0x7fff_ffff) as u32).to_le_bytes().to_vec()),
        suffix,
    );
    n >>= 31;
    while n != 0 {
        let word = (n as u32 & 0x7fff_ffff) | 0x8000_0000;
        result = Bytes::pair(Bytes::Literal(word.to_le_bytes().to_vec()), result);
        n >>= 31;
    }
    result
}

fn read_nat(mut input: &Bytes) -> Option<(usize, &Bytes)> {
    let mut value = 0usize;
    loop {
        let (Bytes::Literal(word), rest) = input.parts()? else {
            return None;
        };
        let group = u32::from_le_bytes(word.as_slice().try_into().ok()?);
        if value == 0 && group == 0x8000_0000 {
            return None;
        }
        value = value
            .checked_mul(1usize << 31)?
            .checked_add((group & 0x7fff_ffff) as usize)?;
        if group < 0x8000_0000 {
            return Some((value, rest));
        }
        input = rest;
    }
}

fn empty() -> Bytes {
    Bytes::Literal(Vec::new())
}

fn field(b: Bytes, suffix: Bytes) -> Option<Bytes> {
    Some(nat(b.length()?, Bytes::pair(b, suffix)))
}

fn read_field(b: &Bytes) -> Option<(&Bytes, &Bytes)> {
    let (len, rest) = read_nat(b)?;
    let (value, suffix) = rest.parts()?;
    if value.length()? == len {
        Some((value, suffix))
    } else {
        None
    }
}

fn fields(elements: &[Bytes]) -> Option<Bytes> {
    let mut result = empty();
    for e in elements.iter().rev() {
        result = field(e.clone(), result)?;
    }
    Some(result)
}

fn hash_node(tag: u8, content: Bytes) -> Bytes {
    Bytes::Hash(Box::new(Bytes::pair(Bytes::Literal(vec![tag]), content)))
}

fn split_width(width: usize) -> usize {
    let mut k = 1;
    while k <= width.saturating_sub(1) / 2 {
        k *= 2;
    }
    k
}

fn root(elements: &[Bytes]) -> Option<Bytes> {
    match elements {
        [] => Some(hash_node(0, empty())),
        [x] => Some(hash_node(1, x.clone())),
        _ => {
            let (left, right) = elements.split_at(split_width(elements.len()));
            Some(hash_node(2, field(root(left)?, root(right)?)?))
        }
    }
}

fn opening(mut elements: &[Bytes], mut index: usize) -> Option<Bytes> {
    let element = elements.get(index)?.clone();
    let original = index;
    let mut path = Vec::new();
    while elements.len() > 1 {
        let k = split_width(elements.len());
        let (left, right) = elements.split_at(k);
        if index < k {
            path.push(root(right)?);
            elements = left;
        } else {
            path.push(root(left)?);
            elements = right;
            index -= k;
        }
    }
    field(element, nat(original, fields(&path)?))
}

fn check_path(element: &Bytes, mut i: usize, mut width: usize, mut path: &Bytes) -> Option<Bytes> {
    let mut siblings = Vec::new();
    while *path != empty() {
        let (sibling, rest) = read_field(path)?;
        let k = split_width(width);
        let left = i < k;
        siblings.push((left, sibling));
        if left {
            width = k;
        } else {
            i -= k;
            width = width.saturating_sub(k);
        }
        path = rest;
    }
    let mut digest = hash_node(1, element.clone());
    while let Some((left, sibling)) = siblings.pop() {
        digest = hash_node(
            2,
            if left {
                field(digest, sibling.clone())?
            } else {
                field(sibling.clone(), digest)?
            },
        );
    }
    Some(digest)
}

pub type Server = String;

use super::roles::{Deductions, Recipe, derive};

pub type Action = super::Action<Server>;

#[derive(Clone, Debug)]
pub enum Entry {
    Network(Bytes),
    Random,
    PublicKey(Server, Bytes),
    SecretKey(Server, Bytes),
    State(Server, Vec<Bytes>),
    ServerAuthenticated(Server, Bytes),
    ClientAccept(Server, Bytes),
    KeyCompromised(Server, Bytes),
    StateCompromised(Server),
}

fn receive(trace: &[Entry], handle: usize) -> Option<&Bytes> {
    if let Entry::Network(msg) = trace.get(handle)? {
        Some(msg)
    } else {
        None
    }
}

impl Deductions for Vec<Entry> {
    type Bytes = Bytes;
    fn receive(&self, h: usize) -> Option<Bytes> {
        receive(self, h).cloned()
    }
    fn literal(&self, b: &[u8]) -> Bytes {
        Bytes::Literal(b.to_vec())
    }
    fn concat(&self, l: Bytes, r: Bytes) -> Bytes {
        Bytes::pair(l, r)
    }
    fn split(&self, b: Bytes, left: bool) -> Option<Bytes> {
        let Bytes::Concat(a, b) = b else { return None };
        Some(if left { *a } else { *b })
    }
    fn hash(&self, b: Bytes) -> Bytes {
        Bytes::Hash(Box::new(b))
    }
    fn vk(&self, k: Bytes) -> Bytes {
        Bytes::VerificationKey(Box::new(k))
    }
    fn sign(&self, k: Bytes, n: Bytes, m: Bytes) -> Bytes {
        Bytes::Signature {
            key: Box::new(k),
            nonce: Box::new(n),
            message: Box::new(m),
        }
    }
}

fn fresh(trace: &mut Vec<Entry>, len: usize) -> Bytes {
    let b = Bytes::Random {
        time: trace.len(),
        len,
    };
    trace.push(Entry::Random);
    b
}

impl super::Execution<Server, Bytes> for Vec<Entry> {
    fn empty() -> Self {
        Vec::new()
    }
    fn send(&mut self, recipe: &Recipe) {
        if let Some(b) = derive(self, recipe) {
            self.push(Entry::Network(b));
        }
    }
    fn random(&mut self, len: usize) {
        let b = fresh(self, len);
        self.push(Entry::Network(b));
    }
    fn generate_key(&mut self, server: &Server) {
        let sk = fresh(self, 32);
        let vk = Bytes::VerificationKey(Box::new(sk.clone()));
        self.push(Entry::Network(vk.clone()));
        self.push(Entry::PublicKey(server.clone(), vk));
        self.push(Entry::SecretKey(server.clone(), sk));
    }
    fn compromise_key(&mut self, handle: usize) {
        let Some(Entry::SecretKey(server, sk)) = self.get(handle).cloned() else {
            return;
        };
        let Some(leak) = field(Bytes::Literal(server.as_bytes().to_vec()), sk.clone()) else {
            return;
        };
        self.push(Entry::KeyCompromised(server, sk));
        self.push(Entry::Network(leak));
    }
    fn compromise_state(&mut self, handle: usize) {
        let Some(Entry::State(server, elements)) = self.get(handle).cloned() else {
            return;
        };
        let Some(state) = fields(&elements) else {
            return;
        };
        let Some(leak) = field(Bytes::Literal(server.as_bytes().to_vec()), state) else {
            return;
        };
        self.push(Entry::StateCompromised(server));
        self.push(Entry::Network(leak));
    }
    fn authenticate(&mut self, server: &Server, messages: &[usize], key: usize) {
        let _ = server_role(self, server, messages, key);
    }
    fn prove_inclusion(&mut self, server: &Server, state: usize, index: usize) {
        let _ = prover_role(self, server, state, index);
    }
    fn check_inclusion(&mut self, server: &Server, signed_root: usize, opening: usize, key: usize) {
        let _ = client_role(self, server, signed_root, opening, key);
    }
}

impl History<Server, Bytes> for Vec<Entry> {
    fn at(&self, server: &Server, element: &Bytes, time: usize) -> Observation {
        match self.get(time) {
            Some(entry) => observe(entry, server, element),
            None => Observation::Other,
        }
    }
}

fn server_role(
    trace: &mut Vec<Entry>,
    server: &Server,
    messages: &[usize],
    key: usize,
) -> Option<()> {
    use super::roles::Server::*;
    let mut elements = Vec::new();
    let (mut signing_key, mut digest, mut nonce, mut signature) = (None, None, None, None);
    for instruction in super::roles::server() {
        match instruction {
            ReceiveAndAuthenticateEachElement => {
                for handle in messages {
                    let b = receive(trace, *handle)?.clone();
                    trace.push(Entry::ServerAuthenticated(server.clone(), b.clone()));
                    elements.push(b);
                }
            }
            LookupSigningKey => {
                let Entry::SecretKey(owner, sk) = trace.get(key)? else {
                    return None;
                };
                if owner != server {
                    return None;
                }
                signing_key = Some(sk.clone());
            }
            ComputeRootAndLength => digest = Some(root(&elements)?),
            GenerateSigningNonce => nonce = Some(fresh(trace, 32)),
            SignRootAndLength => {
                signature = Some(Bytes::Signature {
                    key: Box::new(signing_key.take()?),
                    nonce: Box::new(nonce.take()?),
                    message: Box::new(field(digest.clone()?, nat(elements.len(), empty()))?),
                })
            }
            PublishSignedRoot => {
                let wire = field(
                    digest.take()?,
                    nat(elements.len(), field(signature.take()?, empty())?),
                )?;
                trace.push(Entry::Network(wire));
            }
            StoreElements => trace.push(Entry::State(server.clone(), elements.clone())),
        }
    }
    Some(())
}

fn prover_role(trace: &mut Vec<Entry>, server: &Server, state: usize, index: usize) -> Option<()> {
    use super::roles::Prover::*;
    let mut elements = None;
    for instruction in super::roles::prover() {
        match instruction {
            LoadServerElements => {
                let Entry::State(owner, stored) = trace.get(state)? else {
                    return None;
                };
                if owner != server {
                    return None;
                }
                elements = Some(stored.clone());
            }
            SendOpeningForIndex => trace.push(Entry::Network(opening(elements.as_ref()?, index)?)),
        }
    }
    Some(())
}

fn client_role(
    trace: &mut Vec<Entry>,
    server: &Server,
    signed_root: usize,
    proof: usize,
    key: usize,
) -> Option<()> {
    use super::roles::Client::*;
    let (mut verification_key, mut signed, mut opening) = (None, None, None);
    for instruction in super::roles::client() {
        match instruction {
            LookupVerificationKey => {
                let Entry::PublicKey(owner, vk) = trace.get(key)? else {
                    return None;
                };
                if owner != server {
                    return None;
                }
                verification_key = Some(vk.clone());
            }
            ReceiveSignedRoot => {
                let (digest, rest) = read_field(receive(trace, signed_root)?)?;
                let (len, rest) = read_nat(rest)?;
                let (signature, end) = read_field(rest)?;
                if *end != empty() {
                    return None;
                }
                signed = Some((digest.clone(), len, signature.clone()));
            }
            ReceiveOpening => {
                let (element, rest) = read_field(receive(trace, proof)?)?;
                let (i, path) = read_nat(rest)?;
                // Parse the complete list before checking the signature.
                let mut suffix = path;
                while *suffix != empty() {
                    suffix = read_field(suffix)?.1;
                }
                opening = Some((element.clone(), i, path.clone()));
            }
            VerifyRootSignature => {
                let (digest, len, Bytes::Signature { key, message, .. }) = signed.as_ref()? else {
                    return None;
                };
                let Bytes::VerificationKey(vk) = verification_key.as_ref()? else {
                    return None;
                };
                if vk != key || **message != field(digest.clone(), nat(*len, empty()))? {
                    return None;
                }
            }
            CheckRootFromPath => {
                let (digest, len, _) = signed.as_ref()?;
                let (element, i, path) = opening.as_ref()?;
                if check_path(element, *i, *len, path)? != *digest {
                    return None;
                }
            }
            CheckIndexBounds => {
                if opening.as_ref()?.1 >= signed.as_ref()?.1 {
                    return None;
                }
            }
            LogClientAccept => trace.push(Entry::ClientAccept(
                server.clone(),
                opening.as_ref()?.0.clone(),
            )),
        }
    }
    Some(())
}

/// Execute each action, retaining the trace prefix of a failed action.
pub fn run(actions: &[Action]) -> Vec<Entry> {
    super::execute::<Vec<Entry>, _, Bytes>(actions)
}

pub fn observe(entry: &Entry, server: &str, element: &Bytes) -> Observation {
    use super::Event;
    let event = match entry {
        Entry::ClientAccept(s, e) => Event::ClientAccept {
            same_server: s == server,
            same_element: e == element,
        },
        Entry::ServerAuthenticated(s, e) => Event::ServerAuthenticated {
            same_server: s == server,
            same_element: e == element,
        },
        _ => Event::Other,
    };
    super::classify(
        event,
        matches!(entry, Entry::KeyCompromised(s,_) if s==server),
    )
}

/// Evaluate the authentication statement on an execution from the empty trace.
pub fn check(actions: &[Action], server: &str, element: &Bytes, time: usize) -> bool {
    super::client_authentication::<Vec<Entry>, _, _>(actions, &server.to_owned(), element, time)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(data: &[u8]) -> Bytes {
        Bytes::Literal(data.to_vec())
    }
    fn server() -> Server {
        "server".into()
    }

    fn accept(signed_root: usize, opening: usize) -> Action {
        Action::CheckInclusion {
            server: server(),
            key: 2,
            signed_root,
            opening,
        }
    }

    #[test]
    fn honest_odd_tree_and_replay() {
        let mut actions = vec![Action::GenerateKey(server())];
        for n in 0..5 {
            actions.push(Action::Send(Recipe::Literal(vec![n])));
        }
        actions.push(Action::Authenticate {
            server: server(),
            messages: vec![4, 5, 6, 7, 8],
            key: 3,
        });
        // Authentication events 9..14, nonce 14, signed root 15, state 16.
        actions.push(Action::ProveInclusion {
            server: server(),
            state: 16,
            index: 4,
        });
        actions.push(accept(15, 17));
        actions.push(accept(15, 17));
        let trace = run(&actions);
        assert_eq!(trace.len(), 20);
        for time in [18, 19] {
            assert!(
                matches!(&trace[time], Entry::ClientAccept(s,e) if s == "server" && *e == lit(&[4]))
            );
            assert!(check(&actions, "server", &lit(&[4]), time));
        }
        // A literal cannot parse as a signed root.
        actions.push(accept(4, 17));
        assert_eq!(run(&actions).len(), 20);
    }

    // Build a public symbolic term using only literals and public operations.
    // The key for the forged signature is obtained from the compromise message.
    fn forged(b: Bytes, key: &Recipe) -> Recipe {
        match b {
            Bytes::Literal(data) => Recipe::Literal(data),
            Bytes::Concat(a, b) => {
                Recipe::Concat(Box::new(forged(*a, key)), Box::new(forged(*b, key)))
            }
            Bytes::Hash(x) => Recipe::Hash(Box::new(forged(*x, key))),
            Bytes::Signature { message, .. } => Recipe::Sign(
                Box::new(key.clone()),
                Box::new(Recipe::Literal(vec![])),
                Box::new(forged(*message, key)),
            ),
            _ => panic!("unexpected term in public message"),
        }
    }

    #[test]
    fn compromised_key_can_sign_an_unauthenticated_element() {
        let e = lit(b"new");
        let leaked = Recipe::Right(Box::new(Recipe::Right(Box::new(Recipe::Receive(5)))));
        let digest = root(std::slice::from_ref(&e)).unwrap();
        let sig = Bytes::Signature {
            key: Box::new(empty()),
            nonce: Box::new(empty()),
            message: Box::new(field(digest.clone(), nat(1, empty())).unwrap()),
        };
        let wire = field(digest, nat(1, field(sig, empty()).unwrap())).unwrap();
        let mut actions = vec![
            Action::GenerateKey(server()),
            Action::CompromiseKey(3),
            Action::Send(forged(wire, &leaked)),
            Action::Send(forged(
                opening(std::slice::from_ref(&e), 0).unwrap(),
                &leaked,
            )),
            accept(6, 7),
        ];
        assert!(matches!(&run(&actions)[8],Entry::ClientAccept(_,b) if *b==e));
        assert!(check(&actions, "server", &e, 8));
        // Same element and empty path would reconstruct the same singleton root.
        actions.push(Action::Send(forged(
            field(e, nat(1, empty())).unwrap(),
            &leaked,
        )));
        actions.push(accept(6, 9));
        assert_eq!(run(&actions).len(), 10);
    }

    #[test]
    fn forged_signature_requires_the_registered_key_and_exact_signed_payload() {
        let e = lit(b"new");
        let digest = root(std::slice::from_ref(&e)).unwrap();
        let tbs = field(digest.clone(), nat(1, empty())).unwrap();
        let leaked = Recipe::Right(Box::new(Recipe::Right(Box::new(Recipe::Receive(5)))));
        for (key, payload) in [(Recipe::Literal(vec![]), tbs), (leaked, lit(b"other"))] {
            let sig = Bytes::Signature {
                key: Box::new(empty()),
                nonce: Box::new(empty()),
                message: Box::new(payload),
            };
            let wire = field(digest.clone(), nat(1, field(sig, empty()).unwrap())).unwrap();
            let actions = [
                Action::GenerateKey(server()),
                Action::CompromiseKey(3),
                Action::Send(forged(wire, &key)),
                Action::Send(forged(opening(std::slice::from_ref(&e), 0).unwrap(), &key)),
                accept(6, 7),
            ];
            let trace = run(&actions);
            assert!(matches!(trace.last(), Some(Entry::Network(_))));
            assert_eq!(trace.len(), 8);
        }
    }

    #[test]
    fn witnesses_must_match_and_strictly_precede_acceptance() {
        let e = lit(b"element");
        let trace = vec![
            Entry::StateCompromised(server()),
            Entry::KeyCompromised("elsewhere".into(), empty()),
            Entry::ServerAuthenticated(server(), empty()),
            Entry::ServerAuthenticated("elsewhere".into(), e.clone()),
            Entry::ClientAccept(server(), e.clone()),
            Entry::KeyCompromised(server(), empty()),
            Entry::ServerAuthenticated(server(), e.clone()),
        ];
        assert!(!crate::merkle_authentication::check_history(
            &trace,
            &server(),
            &e,
            4
        ));
        assert!(crate::merkle_authentication::check_history(
            &trace,
            &server(),
            &e,
            usize::MAX
        ));
    }

    #[test]
    fn failed_authentication_retains_events_already_logged() {
        let trace = run(&[
            Action::Send(Recipe::Literal(vec![1])),
            Action::Authenticate {
                server: server(),
                messages: vec![0, 50],
                key: 23,
            },
        ]);
        assert!(
            matches!(&trace[..],[Entry::Network(_), Entry::ServerAuthenticated(_,e)] if *e==lit(&[1]))
        );
    }
}
