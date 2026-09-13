# Host component benchmarks

These Criterion benchmarks execute the real library directly in a `std` host
program. The library remains `no_std`.

## Run

From the repository root:

```sh
# Compile in the bench profile and exercise all fixtures once, without sampling.
cargo bench --locked --bench memory_ops -- --test

# Collect all five benchmarks, including warmup and statistical analysis.
cargo bench --locked --bench memory_ops
```

Criterion writes raw samples and estimates under `target/criterion`, with HTML
reports under the corresponding `report` directories. Each Criterion iteration
performs **100 operations**: its console `time` is for the entire batch, while
`Throughput::Elements(100)` describes the throughput.


Use a fresh baseline name for each complete experiment. On Linux, a quiet host
and a consistent allowed logical CPU help reduce scheduling variation, for example:

```sh
taskset -c 0 cargo bench --locked --bench memory_ops -- --save-baseline experiment_b
```

Choose an allowed CPU on your machine. WSL/VM scheduling and frequency changes
can still affect timings. Record the commit, local diff, Rust version, compiler
flags, CPU, OS and affinity alongside any published results. Defaults are
100 samples, 3 seconds of warmup and a 10-second measurement target per benchmark,
with 95% confidence intervals. Setup and restoration increase total wall time.

## Workload and timing boundaries

All cases run on one thread and use `GlobalAllocator<BitAlloc1M>`, retaining the
production bitmap hierarchy and actual allocator lock. The pool contains 1,024
real 4 KiB frames (4 MiB), initially all free. The remaining bitmap capacity is
unavailable. Initialization allocates zeroed, aligned memory and writes to every
page before measurement to avoid first-touch host page faults during the benchmark.

| Benchmark ID | Timed work per iteration | Preparation and restoration outside timing |
|---|---|---|
| `allocator/alloc/100` | Allocate 100 distinct single frames, retaining their addresses | Register client; return all 100 frames after each batch |
| `allocator/dealloc/100` | Return 100 allocated single frames in allocation order | Allocate the 100 frames before each batch |
| `page_table/map_page/100` | Map 100 consecutive 4 KiB pages in ascending order, starting with only an empty root | Create root once; unmap all 100 pages after each batch |
| `page_table/unmap_page/100` | Unmap the same 100 pages in ascending order, including empty-table pruning/reclamation | Populate the page table before each batch; drop empty root after the benchmark |
| `page_table/query/100` | Query 100 mapped addresses in ascending order, each at offset 17 within its 4 KiB page | Populate once before the benchmark; validate returned virtual/physical bases, size and attributes after each batch; unmap afterwards |

Page-table cases use `ExPageTable<BitAlloc1M, Aarch64PTE>` with three levels of
512 entries (1 GiB / 2 MiB / 4 KiB), and only 4 KiB leaf mappings. The virtual
range starts at `0x1000_0000` and fits in one leaf table. In the map/unmap cases,
the first map in each batch allocates two intermediate tables; the final unmap
reclaims both. Their costs are included and amortized over the batch. The root
is retained between batches. Query keeps the populated table across samples and
measures successful software walks returning the containing mapping's virtual
base, frame base, size and attributes. It performs no allocation or page-table
mutation and does not measure query misses or hardware TLB hits.
These are warmed, dense sequential workloads, not measurements of
isolated cold calls, sparse mappings or contended allocation.

Host pointers to the backing pool are translated to simulated table physical
addresses starting at `0x1000_0000`. Leaf data physical addresses start at
`0x6000_0000` and are only encoded in PTEs and checked by `query`; the benchmark
does not allocate or access guest data memory. Actual page-table accesses always
resolve to the real backing allocation.

The timed loops include loop control, necessary result stores and `black_box`
barriers. They batch timer reads and do not subtract an estimated timer overhead.
Result validation, opposite operations used for restoration, root creation/drop,
pool allocation and allocator initialization are excluded. Before sampling, the
harness checks allocation uniqueness/bounds/zeroing and repeated page-table
map/query/unmap behavior. After sampling, it explicitly drops the empty root and
allocates all pool frames to verify that every frame was returned and cleared.
No allocator is reinitialized while live resources exist.

`Tracked::assume_new()` is used only for the erased initial permission map in
this unverified host harness; subsequent allocator client tokens are passed
through the real APIs. Production code and its proof contracts are unchanged.

## Interpretation

These are **host software timings**. Selecting `Aarch64PTE` selects the PTE
encoding, not the host instruction set: an x86 host runs x86 code. No real
DSB/TLBI, stage-2 activation, guest execution, region management or hvisor adapter
work is included. Use the same platform, compiler settings, workload and timing
boundaries for Native comparisons, including equivalent page-table reclamation
semantics. The report intentionally leaves Native and overhead uncomputed.

The reporting script reads Criterion 0.8 JSON, verifies the five benchmark IDs,
100-element throughput and 95% intervals, and rejects missing or invalid data.
When using a non-default Cargo target directory, pass its Criterion directory
with `--criterion-dir`.

References: [Criterion timing loops](https://bheisler.github.io/criterion.rs/book/user_guide/timing_loops.html)
and [Bencher API](https://docs.rs/criterion/0.8.2/criterion/struct.Bencher.html).
