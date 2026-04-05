# hax-lib-additions

Hax prelude library for Lean 4, extracted from [libcrux-lean-specs](https://github.com/spitters/libcrux-lean-specs).

Provides:
- **Rust primitives** (`Hax.Rust_primitives`): Lean models of Rust integer types, arrays, vectors, ranges, casts, etc.
- **Core models** (`Hax.Core_models`): Lean models of Rust `core` library types (iterators, slices, results, etc.)
- **Missing Lean** (`Hax.MissingLean`): Extensions to the Lean standard library (BitVec, UInt, SInt, etc.)
- **Tactics** (`Hax.Tactic`): Automation for hax-generated code (panic freedom, zify, bv_decide helpers)

## Usage

Add to your `lakefile.lean`:

```lean
require «hax-lib-additions» from git
  "https://github.com/spitters/hax-lib-additions" @ "main"
```

Then import:

```lean
import Hax
```

## License

MIT License (see [LICENSE](LICENSE)).
