# verified-hv-mem
A modular, architecture-independent memory management library for Rust hypervisors, designed for reuse and formal verification with Verus.

Host Criterion benchmarks for single-frame allocation/deallocation and page-table
map/unmap/query are available in [benches/README.md](benches/README.md).

Host region insert/remove and zone-memory create/remove benchmarks matching
hvisor's workload are described in [benches/region_zone.md](benches/region_zone.md).
