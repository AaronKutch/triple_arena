alias t := test
alias r := run
alias c := check

quick:
  cargo fmt
  cargo clippy --all --all-targets --all-features -- -D clippy::all

check:
  cargo check
  cargo clippy --all --all-targets -- -D clippy::all
  cargo doc

test *ARGS:
  cargo nextest run --all-features {{ARGS}}

test_all *ARGS:
  cargo nextest run --all-features {{ARGS}}
  cargo t --doc --all-features {{ARGS}}

test_stable *ARGS:
  # TODO find MSRV and actually set it
  cargo +nightly-2023-04-14 t --all-features {{ARGS}}

bench *ARGS:
  cargo bench -p testcrate {{ARGS}}

run *ARGS:
  cargo r --bin {{ARGS}}

miri *ARGS:
  MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-strict-provenance" cargo miri test --all-features {{ARGS}}

clean:
  cargo clean
