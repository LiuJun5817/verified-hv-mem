# Host region and zone-memory benchmarks

This benchmark runs the **current repository's** `HvMem` implementation directly
on the host. Its region workload and timing boundaries match hvisor's
`tools/memory-bench/benches/region_zone_ops.rs`. This target links the local
library; no sibling checkout is required to build or run it.
Region insert/remove default to **one 1024-page target operation after preparing
32 regions of 1024 pages each**. Zone create/remove
default to **one empty zone per iteration**, using the direct lifecycle APIs.
When comparing with hvisor, use the same workload and timing boundaries in both
repositories.

## Run

From the repository root, with Python 3 and Rust 1.95.0 installed:

```sh
# Full measurements, environment capture, and ns/op reports.
python3 tools/run_region_zone_bench.py

# Measure only empty-zone creation and removal (zero regions is the default).
ZONE_REGIONS=0 python3 tools/run_region_zone_bench.py zone_memory/

# Explicit default region workload, matching hvisor.
PREFILL_REGIONS=32 PREFILL_REGION_PAGES=1024 REGION_PAGES=1024 python3 tools/run_region_zone_bench.py region/

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
PREFILL_REGIONS=3 PREFILL_REGION_PAGES=1 REGION_PAGES=513 ZONE_REGIONS=2 cargo +1.95.0 bench --locked --bench region_zone_ops -- --test
```

The second case checks unequal background/target sizes and a target crossing
a 2 MiB leaf-table boundary, plus the optional populated-zone mode. Direct Cargo
runs do not capture the runner's environment and fresh result directory.

## Workload

| Parameter | Default | Range | Meaning |
|---|---:|---|---|
| `PREFILL_REGIONS` | 32 | 1–4096 | Background CPU regions prepared outside timing |
| `PREFILL_REGION_PAGES` | 1024 | 1–32768 | 4 KiB pages per background region |
| `REGION_PAGES` | 1024 | 1–32768 | 4 KiB pages in the target region; also per region in optional populated-zone cases |
| `ZONE_REGIONS` | 0 | 0–64 | 0 selects direct empty-zone operations; >0 populates this many RAM regions in each CPU/IOMMU set |

The region address range must fit within 65536 pages (256 MiB):
`PREFILL_REGIONS * max(PREFILL_REGION_PAGES, REGION_PAGES) + REGION_PAGES <= 65536`.
Optional populated-zone cases retain the limit
`ZONE_REGIONS * REGION_PAGES <= 32768`. The old batch parameter `REGIONS` is
rejected with migration guidance; unset it before using this workload.
Defaults use 100 samples, 3 seconds of warmup and a 10-second measurement
target per case, with 95% confidence intervals. `ROUNDS` from the bare-metal
benchmark is not used by Criterion.

With `ZONE_REGIONS=0`, zone results are named `zone_memory/create/empty` and
`zone_memory/remove/empty`. `REGION_PAGES` does not affect the empty-zone workload.
Setting `ZONE_REGIONS` above zero retains the populated-zone workload and its
`<count>_regions_<pages>_pages` result names, keeping the two scopes distinct.

The default region IDs are
`region/insert/prefill_32_regions_1024_pages/target_1024_pages` and
`region/remove/after_insert/prefill_32_regions_1024_pages/target_1024_pages`.
They match hvisor and distinguish these results from the earlier empty-set cases.

Each round starts with a fresh zone at ID 1 and an empty payload. Regions are
read/write, non-executable RAM, starting at guest `0x1000_0000` and data physical
`0x6000_0000`. Region slots are separated by
`max(PREFILL_REGION_PAGES, REGION_PAGES)` pages; the target follows all background
slots. With defaults, the background is contiguous and covers 128 MiB, followed
by the 4 MiB target at guest `0x1800_0000`, data physical `0x6800_0000`.
The library uses `GlobalAllocator<BitAlloc1M>`,
`BudgetProtocol`, `VecMemorySet` and `ExPageTable<BitAlloc1M, Aarch64PTE>` with
three levels of 512 entries. Huge pages are disabled, so every mapping uses
4 KiB entries. The 1,024 page-table frames have real aligned, zeroed host backing,
with every page touched before measurement. Leaf data addresses are encoded in
PTEs, not dereferenced by the benchmark.

## Timing boundaries

| Case | Inside the timer | Operations per Criterion iteration |
|---|---|---:|
| `region/insert` | One `HvMem::insert_region` for the target, with the background already present | 1 |
| `region/remove/after_insert` | One `HvMem::remove_region` for the newly inserted target | 1 |
| `zone_memory/create/empty` (default) | Only `HvMem::add_zone` | 1 |
| `zone_memory/remove/empty` (default) | Only `HvMem::remove_zone` on an already empty zone | 1 |
| Populated `zone_memory/create` (`ZONE_REGIONS>0`) | `HvMem::add_zone`, then populate CPU **and IOMMU** RAM mappings | 1 |
| Populated `zone_memory/remove` (`ZONE_REGIONS>0`) | `HvMem::clear`, `clear_iommu`, then `remove_zone` | 1 |

Empty-zone creation includes the library's zone registration, locking, CPU and
IOMMU memory-set initialization, and two root page-table allocations. Empty-zone
removal includes deregistration, locking and reclamation of both root tables.
The empty path performs no region insertion/removal and no `clear` or
`clear_iommu` calls. The operation implementations are selected before timing.
For create, removal and checks happen after the timer; for remove, creating and
checking the empty zone happens before the timer. The manager and frame pool
are reused across iterations, so these are warmed steady-state API costs.

For each region insert iteration, create an empty zone, insert all background
regions and check them before starting the timer. Time only insertion of the
target: with defaults, the CPU set grows from 32 to 33 regions. For remove,
prepare those same 32 background regions and insert the same target before
starting the timer; deletion leaves the original 32 regions intact.

After each timed operation, check the resulting mappings and destroy the whole
zone outside timing. This matches hvisor's full reset on every iteration:
repeatedly removing/reinserting into one surviving set could reuse intermediate
page tables retained by Native and change later insert costs. The manager and
frame-pool backing are reused, but the zone and its page tables are recreated.

For zone cases, the opposite operation used to prepare or restore state is
outside timing. Every reported region/zone iteration is one operation; **do not
divide region times by 32 or 1024**. A populated-zone operation is likewise one
whole zone. Timer overhead is retained rather than subtracted.

Inputs, result checks and mapping checks are outside measured intervals.
The fixture checks metadata and actual page-table translations for CPU/IOMMU
sets, every target page's first and last byte after insertion/removal, zone
removal, and complete allocator frame
recovery, uniqueness and zeroing. It uses real library locks and explicitly
destroys page tables. Assumed erased permissions are confined to the unverified
host fixture's pool initialization and read-only checks while locks are held.

Hardware callbacks are no-ops. These measurements include software locking,
overlap checks, region storage, allocation, mapping and reclamation, but exclude
privileged MMU/SMMU maintenance, the hvisor compatibility adapter, GIC/PCI/IVC
setup, guest execution and CPU startup/shutdown. Zone-memory cases measure empty
memory-context lifecycle by default, or populated memory-context lifecycle when
requested; they do not measure the full hypervisor VM lifecycle.

The existing `memory_ops` benchmark remains separate. Compare region/zone runs
only with matching source versions, work parameters, toolchain/profile and
hardware scope. The hvisor Native fixture calls its owned CPU `MemorySet`'s
`insert/delete` API directly; this fixture calls the real
`HvMem::insert_region/remove_region` APIs, retaining registry lookup and zone
locking. This implementation difference remains part of the measured cost.
