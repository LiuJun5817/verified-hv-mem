//! Identical in hvisor and VeriHyMem; compare.py rejects divergent copies.
//! Only support/mod.rs adapts the native APIs. One iteration is 100 operations.

mod support;

use std::{
    hint::black_box,
    mem::{size_of, MaybeUninit},
    time::{Duration, Instant},
};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use support::{
    Allocation, Fixture, MapResult, Mapping, QueryResult, Table, UnmapResult, PAGE_SIZE,
    POOL_FRAMES,
};

const OPERATIONS: usize = 100;
const GUEST_BASE: usize = 0x1000_0000;
const QUERY_OFFSET: usize = 17;

fn guest_addr(index: usize) -> usize {
    GUEST_BASE + index * PAGE_SIZE
}

fn buffer<T>() -> [MaybeUninit<T>; OPERATIONS] {
    std::array::from_fn(|_| MaybeUninit::uninit())
}

fn check_allocations(fixture: &Fixture, frames: &[MaybeUninit<Allocation>; OPERATIONS]) {
    let mut seen = [false; POOL_FRAMES];
    for slot in frames {
        // SAFETY: called only after every allocation slot was initialized.
        let frame = unsafe { slot.assume_init_ref() };
        assert_eq!(support::allocation_size(frame), PAGE_SIZE);
        let index = fixture.frame_index(frame);
        assert!(!seen[index], "duplicate allocation");
        seen[index] = true;
    }
}

fn prepare_mappings(fixture: &Fixture, table: &mut Table, mappings: &[Mapping; OPERATIONS]) {
    for mapping in mappings {
        support::check_map(&fixture.map(table, mapping));
    }
}

fn check_mappings(fixture: &Fixture, table: &Table) {
    for index in 0..OPERATIONS {
        support::check_query(
            &fixture.query(table, guest_addr(index) + QUERY_OFFSET),
            index,
            QUERY_OFFSET,
        );
    }
}

fn clear_mappings(fixture: &Fixture, table: &mut Table, mappings: &[Mapping; OPERATIONS]) {
    for (index, mapping) in mappings.iter().enumerate() {
        support::check_unmap(&fixture.unmap(table, mapping), index);
    }
}

fn check_unmapped(fixture: &Fixture, table: &Table) {
    for index in 0..OPERATIONS {
        support::check_missing(&fixture.query(table, guest_addr(index) + QUERY_OFFSET));
    }
}

fn allocator_benches(c: &mut Criterion) {
    // Native API layouts may differ; no extra Option/Result wraps these values.
    eprintln!(
        "native sizes: allocation={} map_result={} unmap_result={} query_result={}",
        size_of::<Allocation>(),
        size_of::<MapResult>(),
        size_of::<UnmapResult>(),
        size_of::<QueryResult>()
    );
    let fixture = Fixture::new();
    fixture.assert_all_frames_returned();
    let fixture = black_box(&fixture);
    let mut group = c.benchmark_group("allocator");
    group.throughput(Throughput::Elements(OPERATIONS as u64));

    group.bench_function(BenchmarkId::new("alloc", OPERATIONS), |b| {
        b.iter_custom(|rounds| {
            let mut client = fixture.new_client();
            let mut frames = buffer::<Allocation>();
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                let start = Instant::now();
                for slot in &mut frames {
                    slot.write(fixture.alloc(&mut client));
                }
                elapsed += start.elapsed();
                check_allocations(fixture, black_box(&frames));
                for slot in &mut frames {
                    // SAFETY: initialized above; ownership is consumed once.
                    fixture.dealloc(&mut client, unsafe { slot.assume_init_read() });
                }
            }
            elapsed
        });
    });

    group.bench_function(BenchmarkId::new("dealloc", OPERATIONS), |b| {
        b.iter_custom(|rounds| {
            let mut client = fixture.new_client();
            let mut frames = buffer::<Allocation>();
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                for slot in &mut frames {
                    slot.write(fixture.alloc(&mut client));
                }
                check_allocations(fixture, &frames);
                let input = black_box(&mut frames);
                let start = Instant::now();
                for slot in input {
                    // SAFETY: initialized above; ownership is consumed once.
                    fixture.dealloc(&mut client, unsafe { slot.assume_init_read() });
                }
                elapsed += start.elapsed();
                black_box(fixture);
            }
            elapsed
        });
    });
    group.finish();
    fixture.assert_all_frames_returned();
}

fn page_table_benches(c: &mut Criterion) {
    let fixture = Fixture::new();
    fixture.assert_all_frames_returned();
    let fixture = black_box(&fixture);
    let mappings: [Mapping; OPERATIONS] = std::array::from_fn(support::mapping);
    let addresses: [usize; OPERATIONS] =
        std::array::from_fn(|index| guest_addr(index) + QUERY_OFFSET);

    let mut table = fixture.new_table();
    check_unmapped(fixture, &table);
    for _ in 0..2 {
        prepare_mappings(fixture, &mut table, &mappings);
        for index in 0..OPERATIONS {
            for offset in [0, QUERY_OFFSET, PAGE_SIZE - 1] {
                support::check_query(
                    &fixture.query(&table, guest_addr(index) + offset),
                    index,
                    offset,
                );
            }
        }
        for addr in [GUEST_BASE - 1, guest_addr(OPERATIONS)] {
            support::check_missing(&fixture.query(&table, addr));
        }
        clear_mappings(fixture, &mut table, &mappings);
        check_unmapped(fixture, &table);
    }
    fixture.destroy_table(table);
    fixture.assert_all_frames_returned();

    let mut group = c.benchmark_group("page_table");
    group.throughput(Throughput::Elements(OPERATIONS as u64));
    group.bench_function(BenchmarkId::new("map_page", OPERATIONS), |b| {
        let input = black_box(&mappings);
        b.iter_custom(|rounds| {
            let mut results = buffer::<MapResult>();
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                // Both implementations start with a fresh root every batch.
                let mut table = fixture.new_table();
                let start = Instant::now();
                for (mapping, slot) in input.iter().zip(&mut results) {
                    slot.write(fixture.map(&mut table, black_box(mapping)));
                }
                elapsed += start.elapsed();
                for slot in black_box(&mut results) {
                    // SAFETY: every result was initialized and is consumed once.
                    support::check_map(&unsafe { slot.assume_init_read() });
                }
                check_mappings(fixture, &table);
                clear_mappings(fixture, &mut table, input);
                check_unmapped(fixture, &table);
                fixture.destroy_table(table);
            }
            elapsed
        });
    });

    group.bench_function(BenchmarkId::new("unmap_page", OPERATIONS), |b| {
        let input = black_box(&mappings);
        b.iter_custom(|rounds| {
            let mut results = buffer::<UnmapResult>();
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                let mut table = fixture.new_table();
                prepare_mappings(fixture, &mut table, input);
                check_mappings(fixture, &table);
                let start = Instant::now();
                for (mapping, slot) in input.iter().zip(&mut results) {
                    slot.write(fixture.unmap(&mut table, black_box(mapping)));
                }
                elapsed += start.elapsed();
                for (index, slot) in black_box(&mut results).iter_mut().enumerate() {
                    // SAFETY: every result was initialized and is consumed once.
                    support::check_unmap(&unsafe { slot.assume_init_read() }, index);
                }
                check_unmapped(fixture, &table);
                fixture.destroy_table(table);
            }
            elapsed
        });
    });

    let mut table = fixture.new_table();
    prepare_mappings(fixture, &mut table, &mappings);
    check_mappings(fixture, &table);
    group.bench_function(BenchmarkId::new("query", OPERATIONS), |b| {
        let table = black_box(&table);
        let input = black_box(&addresses);
        b.iter_custom(|rounds| {
            let mut results = buffer::<QueryResult>();
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                let start = Instant::now();
                for (addr, slot) in input.iter().zip(&mut results) {
                    slot.write(fixture.query(table, black_box(*addr)));
                }
                elapsed += start.elapsed();
                for (index, slot) in black_box(&mut results).iter_mut().enumerate() {
                    // SAFETY: every result was initialized and is consumed once.
                    support::check_query(&unsafe { slot.assume_init_read() }, index, QUERY_OFFSET);
                }
            }
            elapsed
        });
    });
    clear_mappings(fixture, &mut table, &mappings);
    check_unmapped(fixture, &table);
    fixture.destroy_table(table);
    group.finish();
    fixture.assert_all_frames_returned();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(100)
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(10))
        .confidence_level(0.95);
    targets = allocator_benches, page_table_benches
}
criterion_main!(benches);
