# The empty default uses whatever cargo is already active, which can come from the nix shell or
# rustup default
#
# - Nix: `nix develop .#nightly -c just check` (or `.#msrv`, or nothing for default pinned)
# - rustup: `just toolchain=nightly check` (or `toolchain=1.85`, etc.)
toolchain := ""
cargo := if toolchain == "" { "cargo" } else { "cargo +" + toolchain }

alias c := check
alias t := test
alias r := run

quick:
  {{cargo}} fmt
  {{cargo}} clippy --all --all-targets --all-features -- -D clippy::all

fix:
  {{cargo}} clippy --fix --all --all-targets --all-features -- -D clippy::all

fmt:
  {{cargo}} sort -w
  {{cargo}} fmt

check:
  {{cargo}} check
  {{cargo}} clippy --all --all-targets -- -D clippy::all

test *ARGS:
  {{cargo}} nextest run --all-features {{ARGS}}

test_all *ARGS:
  {{cargo}} sort -cw
  {{cargo}} doc --no-deps
  {{cargo}} nextest run --all-features {{ARGS}}
  {{cargo}} t --doc --all-features {{ARGS}}
  {{cargo}} r --bin render0
  {{cargo}} r --bin render1
  {{cargo}} r --example equation
  # needs the pinned toolchain
  {{cargo}} b --target=riscv32i-unknown-none-elf -p no_std_test

# Needs to be run with the MSRV toolchain
test_for_msrv:
  {{cargo}} build --no-default-features

miri *ARGS:
  MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-strict-provenance" {{cargo}} miri test --all-features {{ARGS}}

bench *ARGS:
  {{cargo}} bench -p testcrate {{ARGS}}

run *ARGS:
  {{cargo}} r --bin {{ARGS}}

clean:
  {{cargo}} clean

# Print the nix shell's PATH, for VSCode for instance you can add this to get rust-analyzer to work:
# `"rust-analyzer.cargo.extraEnv": {"NIX_PROFILES": "/nix/var/nix/profiles/default ${userHome}/.nix-profile", "PATH": "..."},`
ra_path:
  nix develop .#nightly --command printenv PATH
