<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Ruby → Rust Migration Guide

## Policy
Ruby code should be migrated to Rust for:
- Better memory safety
- Performance improvements
- Static typing

## Migration Steps
1. Create `Cargo.toml` and `src/main.rs`
2. Convert Ruby classes to Rust structs
3. Use `serde` for serialization
4. Remove Gemfile and *.rb files after migration

## Status: PENDING MIGRATION
