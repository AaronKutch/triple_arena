# The empty default uses whatever cargo is already active, which can come from the nix shell or
# rustup default
#
# - Nix: `nix develop .#nightly -c just check` (or `.#msrv`, or nothing for default pinned)
# - rustup: `just toolchain=nightly check` (or `toolchain=1.86`, etc.)
toolchain := ""
cargo := if toolchain == "" { "cargo" } else { "cargo +" + toolchain }
rustc := if toolchain == "" { "rustc" } else { "rustc +" + toolchain }

alias c := check
alias t := test
alias r := run

quick:
  {{cargo}} fmt
  {{cargo}} clippy --all --all-targets --all-features -- -D clippy::all

fix *ARGS:
  {{cargo}} clippy --fix --all --all-targets --all-features {{ARGS}} -- -D clippy::all

fmt:
  {{cargo}} sort -w
  {{cargo}} fmt

check:
  {{cargo}} check
  {{cargo}} clippy --all --all-targets -- -D clippy::all

test *ARGS:
  {{cargo}} nextest run --all-features {{ARGS}}

test_update *ARGS:
  UPDATE_EXPECT=1 {{cargo}} nextest run --all-features {{ARGS}}
  UPDATE_EXPECT=1 {{cargo}} nextest run --release --all-features {{ARGS}}

test_all:
  {{cargo}} sort -cw
  {{cargo}} doc --no-deps --all-features
  {{cargo}} nextest run --no-default-features
  {{cargo}} nextest run --no-default-features --features=alloc
  {{cargo}} nextest run --no-default-features --features=serde_support
  {{cargo}} nextest run --all-features
  {{cargo}} t --doc --all-features
  {{cargo}} r --bin render0 --features=alloc
  {{cargo}} r --bin render1 --features=alloc
  {{cargo}} r --example equation --features=alloc
  {{cargo}} machete
  # needs the pinned toolchain
  {{cargo}} b --target=riscv32i-unknown-none-elf -p no_std_test
  (cd ./no_alloc_test && {{cargo}} b --target=riscv32i-unknown-none-elf -p no_alloc_test)

# Needs to be run with the MSRV toolchain
test_for_msrv:
  {{cargo}} b -p triple_arena --no-default-features
  {{cargo}} b -p triple_arena --all-features
  {{cargo}} b -p triple_arena_render

miri *ARGS:
  MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-strict-provenance" {{cargo}} miri test --all-features {{ARGS}}

bench *ARGS:
  {{cargo}} bench -p testcrate --features=alloc {{ARGS}}

run *ARGS:
  {{cargo}} r --bin {{ARGS}}

doc *ARGS:
  {{cargo}} doc --open {{ARGS}}

clean:
  {{cargo}} clean

# Print the nix shell's PATH, for VSCode for instance you can add this to get rust-analyzer to work:
# `"rust-analyzer.cargo.extraEnv": {"NIX_PROFILES": "/nix/var/nix/profiles/default ${userHome}/.nix-profile", "PATH": "..."},`
ra_path:
  nix develop .#nightly --command printenv PATH

# equivalent to `rustup doc`
std_doc:
  xdg-open "$({{rustc}} --print sysroot)/share/doc/rust/html/index.html"
