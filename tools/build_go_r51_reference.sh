#!/bin/sh
# Build the pinned Go reference image for the Go-linked leaf proofs.
#
# Usage: tools/build_go_r51_reference.sh OUTPUT_DIRECTORY
#
# Fetches the narya-ed25519 module at the commit the committed Lean inputs
# were generated from, builds its r51x5 package test binary twice with the
# pinned toolchain, requires the two builds to be byte-identical, and also
# builds a stripped (-s -w) variant. Writes r51x5.test and
# r51x5.stripped.test to OUTPUT_DIRECTORY.
#
# Needs git and a Go toolchain new enough to honour GOTOOLCHAIN (1.21 or
# later); the pinned toolchain is downloaded and checksum-verified by the Go
# command itself.
set -eu

MODULE_URL=https://github.com/Overclock-Validator/narya-ed25519.git
MODULE_COMMIT=c265ee9667131a556cd332c252b79de0860c7640
TOOLCHAIN=go1.27.3

if [ "$#" -ne 1 ]; then
    echo "usage: $0 OUTPUT_DIRECTORY" >&2
    exit 2
fi
mkdir -p "$1"
output=$(cd "$1" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

git -C "$work" init -q module
git -C "$work/module" fetch -q --depth 1 "$MODULE_URL" "$MODULE_COMMIT"
git -C "$work/module" checkout -q --detach FETCH_HEAD
test "$(git -C "$work/module" rev-parse HEAD)" = "$MODULE_COMMIT"

build() {
    (
        cd "$work/module"
        GOOS=linux GOARCH=amd64 GOTOOLCHAIN=$TOOLCHAIN CGO_ENABLED=0 \
            go test -c -trimpath -buildvcs=false -ldflags="$1" -o "$2" ./internal/r51x5
    )
}

build -buildid= "$work/first.test"
build -buildid= "$work/second.test"
if ! cmp -s "$work/first.test" "$work/second.test"; then
    echo "Go reference build is not reproducible" >&2
    exit 1
fi
build "-s -w -buildid=" "$work/stripped.test"

cp "$work/first.test" "$output/r51x5.test"
cp "$work/stripped.test" "$output/r51x5.stripped.test"
(cd "$work/module" && GOTOOLCHAIN=$TOOLCHAIN go version)
echo "module commit $MODULE_COMMIT"
if command -v sha256sum >/dev/null 2>&1; then
    (cd "$output" && sha256sum r51x5.test r51x5.stripped.test)
else
    (cd "$output" && shasum -a 256 r51x5.test r51x5.stripped.test)
fi
