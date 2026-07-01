# Alerus

Run verification with
```
cargo verus verify
```

Or, you can build the dependency with `./opendp.sh` 
and then run with verus binary:
```
verus alerus/lib.rs -L dependency=target/release/deps/ --extern random=target/release/librandom.rlib --crate-type=lib
```

Importantly, alerus is incompatible with [`vstd::proph::Prophecy`](https://verus-lang.github.io/verus/verusdoc/vstd/proph/index.html), see [the prophecy paradox](./alerus/proph_paradox.rs), but are compatible with `vstd::proph::ProphecyGhost`, as the later prevents prophetic values from entering a Ghost function.

To ensure soundness of the alerus library, we have a crate-wide clippy lint ban on `vstd::proph::Prophecy`.

