# Host region and zone-memory benchmarks

This benchmark runs the **current repository's** `HvMem` implementation directly
on the host. Its fixture and timed loops follow hvisor's
`tools/memory-bench/src/lib.rs` and `benches/region_zone_ops.rs`, respectively.
The hvisor tool uses a pinned VeriHyMem dependency; this target links the local
library instead. No sibling checkout is required to build or run this benchmark.
Region insert/remove default to **one region per iteration**. When comparing
with hvisor, explicitly use the same `REGIONS` value in both repositories.

## Run

From the repository root, with Python 3 and Rust 1.95.0 installed:

```sh
# Full measurements, environment capture, and ns/op reports.
python3 tools/run_region_zone_bench.py

# Optional override for a larger workload matching hvisor's 100-region case.
REGIONS=100 REGION_PAGES=1 ZONE_REGIONS=4 python3 tools/run_region_zone_bench.py

# Filters and Criterion options are passed through.
python3 tools/run_region_zone_bench.py region/
python3 tools/run_region_zone_bench.py --test
```

The runner builds with Rust **1.95.0**, Criterion **0.8.2**, the explicit host
target and the checked-in lockfile. It builds offline; if the Cargo cache is
empty, first run `cargo +1.95.0 fetch --locked`. The existing bench profile is
opt-level 3, thin LTO, one codegen unit, with debug assertions, overflow checks
and incremental builds disabled, matching the hvisor host benchmark profile.

Only the benchmark process is pinned to the first allowed logical CPU on Linux;
set `BENCH_CPU` to choose another allowed CPU. Compilation and the calling shell
keep their CPU affinity. The environment report records the actual toolchain,
compiler environment, workload, CPU affinity, source revision and source hashes.
CPU pinning does not remove WSL/VM scheduling or frequency variation.

Each invocation gets a fresh directory under `target/region-zone-bench/runs/`.
It contains `environment.json`, `summary.json`, `results.csv`, `report.md`, a run
log, and `criterion/` samples/estimates/reports. Filtered and test-only runs do
not borrow results from earlier runs. The CSV and report normalize Criterion's
**mean** and confidence bounds to `ns/op`; raw console `time` can use a regression
estimate instead. Confidence intervals describe estimated mean times, not
individual-operation latency percentiles.

A direct smoke check is also available:

```sh
cargo +1.95.0 bench --locked --bench region_zone_ops -- --test
REGIONS=3 REGION_PAGES=513 ZONE_REGIONS=2 cargo +1.95.0 bench --locked --bench region_zone_ops -- --test
```

The second case checks multiple regions and mappings crossing a 2 MiB leaf-table
boundary. Direct Cargo runs do not capture the runner's environment and fresh
result directory.

## Workload

| Parameter | Default | Range | Meaning |
|---|---:|---|---|
| `REGIONS` | 1 | 1–4096 | Operations in each region insert/remove batch |
| `REGION_PAGES` | 1 | 1–32768 | 4 KiB pages per region |
| `ZONE_REGIONS` | 1 | 1–64 | RAM regions in each zone-memory case |

Both `REGIONS * REGION_PAGES` and `ZONE_REGIONS * REGION_PAGES` must be at most
32768. Defaults use 100 samples, 3 seconds of warmup and a 10-second measurement
target per case, with 95% confidence intervals. `ROUNDS` from the bare-metal
benchmark is not used by Criterion.

Each round starts with a fresh zone at ID 1 and an empty payload. Regions are
contiguous, read/write, non-executable RAM, starting at guest `0x1000_0000` and
data physical `0x6000_0000`. The library uses `GlobalAllocator<BitAlloc1M>`,
`BudgetProtocol`, `VecMemorySet` and `ExPageTable<BitAlloc1M, Aarch64PTE>` with
three levels of 512 entries. Huge pages are disabled, so every mapping uses
4 KiB entries. The 1,024 page-table frames have real aligned, zeroed host backing,
with every page touched before measurement. Leaf data addresses are encoded in
PTEs, not dereferenced by the benchmark.

## Timing boundaries

| Case | Inside the timer | Operations per Criterion iteration |
|---|---|---:|
| `region/insert` | `HvMem::insert_region` for each CPU region | `REGIONS` |
| `region/remove` | `HvMem::remove_region` for each CPU region | `REGIONS` |
| `zone_memory/create` | `HvMem::add_zone`, then populate CPU **and IOMMU** RAM mappings | 1 |
| `zone_memory/remove` | `HvMem::clear`, `clear_iommu`, then `remove_zone` | 1 |

For region cases, creating the empty zone, preparing removal inputs and finally
destroying the zone are outside timing. For zone cases, the opposite operation
used to prepare or restore state is outside timing. A zone operation is one
**whole zone**, even if `ZONE_REGIONS` exceeds one; never divide its time by the
number of RAM regions. Region batch times are divided by `REGIONS`.
With the default `REGIONS=1`, each region timer covers one insertion or removal,
and Criterion's per-iteration time is already the per-operation time. Insertion
starts from an empty CPU memory set; removal starts with exactly one region.
Necessary intermediate-table allocation/reclamation is fully charged to that
operation rather than amortized over a 100-region batch.
As in the hvisor host benchmark, zone cases time one operation per interval;
timer, loop and result-storage overhead is retained rather than subtracted.

Inputs, result checks and mapping checks are outside measured intervals.
The fixture checks metadata and actual page-table translations for CPU/IOMMU
sets, repeated lifecycle reuse, zone removal, and complete allocator frame
recovery, uniqueness and zeroing. It uses real library locks and explicitly
destroys page tables. Assumed erased permissions are confined to the unverified
host fixture's pool initialization and read-only checks while locks are held.

Hardware callbacks are no-ops. These measurements include software locking,
overlap checks, region storage, allocation, mapping and reclamation, but exclude
privileged MMU/SMMU maintenance, the hvisor compatibility adapter, GIC/PCI/IVC
setup, guest execution and CPU startup/shutdown. Zone-memory cases therefore
measure populated memory-context lifecycle, not the full hypervisor VM lifecycle.

The existing `memory_ops` benchmark remains separate. Compare region/zone runs
only with matching source versions, work parameters, toolchain/profile and
hardware scope; a hvisor host run using another VeriHyMem revision is not a
Native hvisor implementation baseline.
