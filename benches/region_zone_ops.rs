//! Current-repository HvMem software operations using hvisor's timing boundaries.
//! Hardware maintenance is excluded on hosts.

mod region_zone_support;

use std::{
    hint::black_box,
    time::{Duration, Instant},
};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use region_zone_support::{mapping, Fixture, Mapping, OpResult, PAGE_SIZE};

struct Workload {
    regions: usize,
    zone_regions: usize,
    pages: usize,
}

fn parameter(name: &str, default: usize, max: usize) -> usize {
    let value = std::env::var(name)
        .map(|text| text.parse::<usize>().expect("invalid benchmark parameter"))
        .unwrap_or(default);
    assert!((1..=max).contains(&value), "invalid {name}");
    value
}

impl Workload {
    fn new() -> Self {
        let workload = Self {
            regions: parameter("REGIONS", 1, 4096),
            zone_regions: parameter("ZONE_REGIONS", 1, 64),
            pages: parameter("REGION_PAGES", 1, 32768),
        };
        assert!(workload.regions * workload.pages <= 32768);
        assert!(workload.zone_regions * workload.pages <= 32768);
        workload
    }

    fn mappings(&self, count: usize) -> Vec<Mapping> {
        (0..count).map(|index| mapping(index, self.pages)).collect()
    }

    fn id(&self, count: usize) -> String {
        format!("{count}_regions_{}_pages", self.pages)
    }
}

fn check_results(results: &[OpResult]) {
    for result in results {
        assert!(result.is_ok(), "region operation failed");
    }
}

fn populate(fixture: &Fixture, mappings: &[Mapping]) {
    for region in mappings {
        fixture.insert(region).expect("region setup failed");
    }
}

fn region_benches(c: &mut Criterion) {
    let workload = Workload::new();
    let mappings = workload.mappings(workload.regions);
    let fixture = Fixture::new();
    fixture.assert_all_frames_returned();

    // Check complete lifecycle and reuse before warmup, outside measurements.
    for _ in 0..2 {
        fixture.add_empty_zone().unwrap();
        fixture.check_empty();
        populate(&fixture, &mappings);
        fixture.check_mappings(&mappings);
        for region in &mappings {
            fixture.remove(region).unwrap();
        }
        fixture.check_empty();
        fixture.remove_zone().unwrap();
        fixture.check_removed();
    }
    fixture.assert_all_frames_returned();

    let fixture = black_box(&fixture);
    let input = black_box(mappings.as_slice());
    let mut group = c.benchmark_group("region");
    // Criterion time is per batch. Throughput and the runner's summary use ops.
    group.throughput(Throughput::Elements(workload.regions as u64));
    group.bench_function(
        BenchmarkId::new("insert", workload.id(workload.regions)),
        |b| {
            b.iter_custom(|rounds| {
                let mut results = vec![Ok(()); workload.regions];
                let mut elapsed = Duration::ZERO;
                for _ in 0..rounds {
                    fixture.add_empty_zone().expect("zone setup failed");
                    let start = Instant::now();
                    for (region, result) in input.iter().zip(&mut results) {
                        *result = fixture.insert(black_box(region));
                    }
                    elapsed += start.elapsed();
                    check_results(black_box(&results));
                    fixture.check_mappings(input);
                    fixture.remove_zone().expect("zone cleanup failed");
                    fixture.check_removed();
                }
                elapsed
            });
        },
    );
    group.bench_function(
        BenchmarkId::new("remove", workload.id(workload.regions)),
        |b| {
            b.iter_custom(|rounds| {
                let mut results = vec![Ok(()); workload.regions];
                let mut elapsed = Duration::ZERO;
                for _ in 0..rounds {
                    fixture.add_empty_zone().expect("zone setup failed");
                    populate(fixture, input);
                    fixture.check_mappings(input);
                    let start = Instant::now();
                    for (region, result) in input.iter().zip(&mut results) {
                        *result = fixture.remove(black_box(region));
                    }
                    elapsed += start.elapsed();
                    check_results(black_box(&results));
                    fixture.check_empty();
                    fixture.remove_zone().expect("zone cleanup failed");
                    fixture.check_removed();
                }
                elapsed
            });
        },
    );
    group.finish();
    fixture.assert_all_frames_returned();
}

fn zone_benches(c: &mut Criterion) {
    let workload = Workload::new();
    let mappings = workload.mappings(workload.zone_regions);
    let fixture = Fixture::new();
    fixture.assert_all_frames_returned();
    for _ in 0..2 {
        fixture.create_zone(&mappings).unwrap();
        fixture.check_zone(&mappings);
        fixture.remove_zone().unwrap();
        fixture.check_removed();
    }
    fixture.assert_all_frames_returned();

    let fixture = black_box(&fixture);
    let input = black_box(mappings.as_slice());
    let mut group = c.benchmark_group("zone_memory");
    group.throughput(Throughput::Elements(1));
    group.bench_function(
        BenchmarkId::new("create", workload.id(workload.zone_regions)),
        |b| {
            b.iter_custom(|rounds| {
                let mut elapsed = Duration::ZERO;
                for _ in 0..rounds {
                    let start = Instant::now();
                    let result = fixture.create_zone(input);
                    elapsed += start.elapsed();
                    black_box(result).expect("zone create failed");
                    fixture.check_zone(input);
                    fixture.remove_zone().expect("zone cleanup failed");
                    fixture.check_removed();
                }
                elapsed
            });
        },
    );
    group.bench_function(
        BenchmarkId::new("remove", workload.id(workload.zone_regions)),
        |b| {
            b.iter_custom(|rounds| {
                let mut elapsed = Duration::ZERO;
                for _ in 0..rounds {
                    fixture.create_zone(input).expect("zone setup failed");
                    fixture.check_zone(input);
                    let start = Instant::now();
                    let result = fixture.remove_zone();
                    elapsed += start.elapsed();
                    black_box(result).expect("zone remove failed");
                    fixture.check_removed();
                }
                elapsed
            });
        },
    );
    group.finish();
    fixture.assert_all_frames_returned();
}

fn configured_criterion() -> Criterion {
    let workload = Workload::new();
    eprintln!(
        "Host software benchmark: regions={}, zone_regions={}, bytes/region={}; hardware maintenance excluded",
        workload.regions, workload.zone_regions, workload.pages * PAGE_SIZE
    );
    Criterion::default()
        .sample_size(100)
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(10))
        .confidence_level(0.95)
}

criterion_group! {
    name = benches;
    config = configured_criterion();
    targets = region_benches, zone_benches
}
criterion_main!(benches);
