#!/bin/sh
# Use hax's Charon and Aeneas with the native Aeneas library used by our proofs.
set -eu
cd "$(dirname "$0")"
charon_version=nightly-2026.10.31
aeneas_version=build-2b9e3ea
tools_dir=${XDG_CACHE_HOME:-"$HOME/.cache"}/hax/tools
cargo hax tools install "charon@$charon_version"
cargo hax tools install "aeneas@$aeneas_version"
charon="$tools_dir/charon/$charon_version/charon"
aeneas="$tools_dir/aeneas/$aeneas_version/aeneas"

# hax-lib's target crate and its host proc macros must both see cfg(hax).
# hax_compilation enables the macros' contract metadata in the examples crate.
mkdir -p ../../target/llbc
llbc_dir=$(cd ../../target/llbc && pwd)
stage=$(mktemp -d "$llbc_dir/extract.XXXXXX")
trap 'rm -rf "$stage"' EXIT
llbc="$stage/examples.llbc"
(cd .. && RUSTFLAGS="--cfg hax -Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(_hax) -Zcrate-attr=register_tool(charon)" \
  "$charon" cargo --preset=aeneas --dest-file "$llbc" \
    --rustc-arg=--cfg=hax_compilation --rustc-arg=--cfg=hax_backend_lean -- \
    -Zhost-config -Ztarget-applies-to-host \
    --config 'host.rustflags=["--cfg","hax","--cfg","hax_backend_lean"]' --locked)

# `hax-step` emits the extracted pre/postconditions and Aeneas step triples.
# The completed contracts live in RustExamples.Merkle and RustExamples.MerkleAuthentication.
"$aeneas" -backend lean -split-files -loops-to-rec -specs hax-step \
  -extra-includes RustExamples.Hax -external-names hax-models.json \
  -dest "$stage" -subdir RustExamples/Gen "$llbc"
mkdir -p RustExamples/Gen
for name in Types Funs Specs; do
  cp "$stage/RustExamples/Gen/$name.lean" "RustExamples/Gen/$name.lean"
done
