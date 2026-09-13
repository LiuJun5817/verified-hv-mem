# Matched host memory benchmarks

`memory_ops.rs` is byte-identical to hvisor's
`tools/memory-bench/benches/memory_ops.rs`. Only `support/mod.rs` adapts the native
allocator/page-table APIs. Production library code is unchanged.

For a valid comparison, run from the sibling **hvisor** repository:

```sh
make compare_memory_ops MEMORY_BENCH_REFERENCE=../verified-hv-mem
```

The runner requires Python 3.11 and Rust 1.95.0 (or explicitly select another
installed toolchain for both implementations). It checks identical harness
bytes, the full Criterion 0.8.2 dependency graph/checksums, profile settings and
compiled Criterion features. It builds both before measurement in a neutral
working directory with the same controlled compiler environment, pins both to
the same allowed logical CPU, and runs A/B followed by B/A. A fresh output
directory contains source/environment/binary hashes, raw samples, CSV and report.
See `../hvisor/tools/memory-bench/README.md` from this repository root for details.

Both profiles use opt-level 3, thin LTO, one codegen unit, and disabled debug
assertions, overflow checks and incremental builds. The paired report uses
Criterion **mean / 100** and **95% CI / 100** for both implementations, reporting
runs separately without pooling confidence intervals. A case has 100 samples,
3 seconds of warmup, a 10-second measurement target, and 100 operations per
iteration. Criterion's console time may use slope, so use the exported mean
when comparing the two implementations.

A standalone smoke check is still available:

```sh
cargo +1.95.0 bench --locked --bench memory_ops -- --test
```

For statistical comparisons use the paired runner, which also checks and clears
compiler environment overrides. Standalone runs do not enforce cross-repository
consistency.

The common workload uses 1,024 backed 4 KiB frames, three AArch64 page-table
levels of 512 entries, 100 consecutive 4 KiB mappings starting at virtual
0x1000_0000 / data physical 0x6000_0000, and query offset 17. Inputs are prepared
outside timing. Both implementations create a fresh root before **each** timed
map/unmap batch and destroy it afterward, outside timing. Query reuses one
populated table. Preparation, checks, inverse operations, root construction and
final destruction are outside the timers in identical order.

Common MaybeUninit buffers retain native allocation and result values, without
an additional Option/Result wrapper or old-value destructor in the measured
loop. Native query results are checked and interpreted only after timing.
Bounds, uniqueness, repeated mapping/query/unmapping and complete frame recovery
are checked. VeriHyMem-specific zero-frame checks run only before/after groups.
The initial erased permission map and temporary empty tracked-token placeholder
are assumed only in this unverified host harness; actual client tokens are
passed through the APIs and their returned successors are retained.

Native semantics remain distinct: both allocators lock; hvisor also locks each
page-table operation. hvisor clears intermediate tables during map and retains
them until table destruction; VeriHyMem clears/reclaims empty tables during
unmap. Native ownership/result layouts also differ and are printed in run logs.
These are host software API costs, excluding hardware TLB/EL2 execution, not
identical reclamation work or full page-table lifecycle costs. CPU pinning and
alternating order cannot eliminate WSL scheduling/frequency variation. Earlier
reports with different harnesses/toolchains are not matched baselines.
