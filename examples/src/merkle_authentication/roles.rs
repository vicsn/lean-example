//! Programs for the honest roles. Each instruction runs in order. A failed
//! lookup, parse, or guard stops that role, preserving its earlier entries.

pub enum Client {
    LookupVerificationKey,
    ReceiveSignedRoot,
    ReceiveOpening,
    /// Verify the signature on the serialized root and leaf count with the
    /// verification key registered for the server named in this action.
    VerifyRootSignature,
    /// Reconstruct the root from the element, root-first siblings, index and
    /// signed count. Require equality with the signed root.
    CheckRootFromPath,
    /// Require the zero-based index to be less than the signed leaf count.
    CheckIndexBounds,
    LogClientAccept,
}

pub fn client() -> [Client; 7] {
    use Client::*;
    [
        LookupVerificationKey,
        ReceiveSignedRoot,
        ReceiveOpening,
        VerifyRootSignature,
        CheckRootFromPath,
        CheckIndexBounds,
        LogClientAccept,
    ]
}

pub enum Server {
    ReceiveAndAuthenticateEachElement,
    LookupSigningKey,
    ComputeRootAndLength,
    GenerateSigningNonce,
    SignRootAndLength,
    PublishSignedRoot,
    StoreElements,
}

pub fn server() -> [Server; 7] {
    use Server::*;
    [
        ReceiveAndAuthenticateEachElement,
        LookupSigningKey,
        ComputeRootAndLength,
        GenerateSigningNonce,
        SignRootAndLength,
        PublishSignedRoot,
        StoreElements,
    ]
}

pub enum Prover {
    LoadServerElements,
    SendOpeningForIndex,
}

pub fn prover() -> [Prover; 2] {
    [Prover::LoadServerElements, Prover::SendOpeningForIndex]
}

/// The attacker may use public constructors and decompose a concatenation.
/// Reading a handle succeeds only for an existing network message.
#[cfg_attr(not(hax), derive(Clone))]
pub enum Recipe {
    Receive(usize),
    Literal(Vec<u8>),
    Concat(Box<Recipe>, Box<Recipe>),
    Left(Box<Recipe>),
    Right(Box<Recipe>),
    Hash(Box<Recipe>),
    VerificationKey(Box<Recipe>),
    Sign(Box<Recipe>, Box<Recipe>, Box<Recipe>),
}

pub(crate) trait Deductions {
    type Bytes;
    fn receive(&self, handle: usize) -> Option<Self::Bytes>;
    fn literal(&self, data: &[u8]) -> Self::Bytes;
    fn concat(&self, left: Self::Bytes, right: Self::Bytes) -> Self::Bytes;
    fn split(&self, input: Self::Bytes, left: bool) -> Option<Self::Bytes>;
    fn hash(&self, input: Self::Bytes) -> Self::Bytes;
    fn vk(&self, key: Self::Bytes) -> Self::Bytes;
    fn sign(&self, key: Self::Bytes, nonce: Self::Bytes, message: Self::Bytes) -> Self::Bytes;
}

// Explicit matches translate directly to the Aeneas option model.
#[allow(clippy::question_mark)]
pub(crate) fn derive<D: Deductions>(world: &D, r: &Recipe) -> Option<D::Bytes> {
    match r {
        Recipe::Receive(h) => world.receive(*h),
        Recipe::Literal(b) => Some(world.literal(b)),
        Recipe::Concat(a, b) => {
            let Some(a) = derive(world, a) else {
                return None;
            };
            let Some(b) = derive(world, b) else {
                return None;
            };
            Some(world.concat(a, b))
        }
        Recipe::Left(x) | Recipe::Right(x) => {
            let Some(x) = derive(world, x) else {
                return None;
            };
            world.split(x, matches!(r, Recipe::Left(_)))
        }
        Recipe::Hash(x) => {
            let Some(x) = derive(world, x) else {
                return None;
            };
            Some(world.hash(x))
        }
        Recipe::VerificationKey(x) => {
            let Some(x) = derive(world, x) else {
                return None;
            };
            Some(world.vk(x))
        }
        Recipe::Sign(k, n, m) => {
            let Some(k) = derive(world, k) else {
                return None;
            };
            let Some(n) = derive(world, n) else {
                return None;
            };
            let Some(m) = derive(world, m) else {
                return None;
            };
            Some(world.sign(k, n, m))
        }
    }
}
