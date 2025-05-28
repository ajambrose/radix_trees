# Radix Trees
This is an implementation of various types of radix trees in Rust.

# Overview
`radix_trees` currently provides a Patricia tree implementation, `PTreeMap`.
This allows associative storage of common-prefix keys with arbitrary values.
See the [documentation](https://docs.rs/radix_trees) for more information.

# no_std
`radix_trees` is `no_std` with `alloc` by default, and doesn't currently
require an `std` trait to enable additional functionality.

# Cargo Features
* `zerocopy`: `radix_trees` enables the `zerocopy` feature by default
(and therefore depends on [zerocopy](https://crates.io/crates/zerocopy)).
This feature can optionally be disabled, with a reduced default set of supported key
types and no helper macro to implement the key trait using `zerocopy`.

# Versioning
Until `radix_trees` reaches version 1.0, breaking changes may occur every minor release (0.X -> 0.Y).
Patch releases (0.A.X -> 0.A.Y) will only contain new APIs, unit tests, or bug fixes.
