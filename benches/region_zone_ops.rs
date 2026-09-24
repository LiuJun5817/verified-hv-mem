//! Current-repository HvMem region and empty/populated zone software operations.
//! Hardware maintenance is excluded on hosts.

mod region_zone_support;

use std::{
    hint::black_box,
    time::{Duration, Instant},
};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use region_zone_support::{mapping, mapping_at, Fixture, Mapping, OpResult, PAGE_SIZE};

struct Workload {
    prefill_regions: usize,
    prefill_pages: usize,
    target_pages: usize,
    zone_regions: usize,
}

fn parameter(name: &str, default: usize, min: usize, max: usize) -> usize {
    let value = std::env::var(name)
        .map(|text| text.parse::<usize>().expect("invalid benchmark parameter"))
        .unwrap_or(default);
    assert!((min..=max).contains(&value), "invalid {name}");
    value
}

impl Workload {
    fn new() -> Self {
        assert!(
            std::env::var_os("REGIONS").is_none(),
            "REGIONS is no longer supported: use PREFILL_REGIONS and PREFILL_REGION_PAGES for region setup"
        );
        let workload = Self {
            prefill_regions: parameter("PREFILL_REGIONS", 32, 1, 4096),
            prefill_pages: parameter("PREFILL_REGION_PAGES", 1024, 1, 32768),
            target_pages: parameter("REGION_PAGES", 1024, 1, 32768),
            zone_regions: parameter("ZONE_REGIONS", 0, 0, 64),
        };
        assert!(
            workload.prefill_regions * workload.stride() + workload.target_pages <= 65536,
            "prefill slots and the insertion target exceed the 256 MiB test range"
        );
        assert!(workload.zone_regions * workload.target_pages <= 32768);
        workload
    }

    fn stride(&self) -> usize {
        self.prefill_pages.max(self.target_pages)
    }

    fn background(&self) -> Vec<Mapping> {
        (0..self.prefill_regions)
            .map(|index| mapping_at(index * self.stride(), self.prefill_pages))
            .collect()
    }

    fn target(&self) -> Mapping {
        mapping_at(self.prefill_regions * self.stride(), self.target_pages)
    }

    fn id(&self) -> String {
        format!(
            "prefill_{}_regions_{}_pages/target_{}_pages",
            self.prefill_regions, self.prefill_pages, self.target_pages
        )
    }

    fn zone_mappings(&self) -> Vec<Mapping> {
        (0..self.zone_regions)
            .map(|index| mapping(index, self.target_pages))
            .collect()
    }

    fn zone_id(&self) -> String {
        format!("{}_regions_{}_pages", self.zone_regions, self.target_pages)
    }
}

fn populate(fixture: &Fixture, mappings: &[Mapping]) {
    for region in mappings {
        fixture.insert(region).expect("region setup failed");
    }
}

fn region_benches(c: &mut Criterion) {
    let workload = Workload::new();
    let background = workload.background();
    let insert_target = workload.target();
    let fixture = Fixture::new();
    fixture.assert_all_frames_returned();

    // Check the complete N -> N+1 -> N lifecycle before warmup.
    fixture.add_empty_zone().unwrap();
    populate(&fixture, &background);
    fixture.check_mappings(&background);
    fixture.insert(&insert_target).unwrap();
    fixture.check_mappings(background.iter().chain(std::iter::once(&insert_target)));
    fixture.check_region_pages(&insert_target, true);
    fixture.remove(&insert_target).unwrap();
    fixture.check_mappings(&background);
    fixture.check_region_pages(&insert_target, false);
    fixture.remove_zone().unwrap();
    fixture.check_removed();
    fixture.assert_all_frames_returned();

    let fixture = black_box(&fixture);
    let background = black_box(background.as_slice());
    let insert_target = black_box(&insert_target);
    let mut group = c.benchmark_group("region");
    // The prefill size and page count do not change the one-operation divisor.
    group.throughput(Throughput::Elements(1));
    group.bench_function(BenchmarkId::new("insert", workload.id()), |b| {
        b.iter_custom(|rounds| {
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                fixture.add_empty_zone().expect("zone setup failed");
                populate(fixture, background);
                fixture.check_mappings(background);
                let start = Instant::now();
                let result = fixture.insert(black_box(insert_target));
                elapsed += start.elapsed();
                black_box(result).expect("region insert failed");
                fixture.check_mappings(background.iter().chain(std::iter::once(insert_target)));
                fixture.check_region_pages(insert_target, true);
                // Match hvisor: fully destroy the sets so retained page tables
                // cannot change the next iteration's starting state.
                fixture.remove_zone().expect("zone cleanup failed");
                fixture.check_removed();
            }
            elapsed
        });
    });
    group.bench_function(
        BenchmarkId::new("remove", format!("after_insert/{}", workload.id())),
        |b| {
            b.iter_custom(|rounds| {
                let mut elapsed = Duration::ZERO;
                for _ in 0..rounds {
                    fixture.add_empty_zone().expect("zone setup failed");
                    populate(fixture, background);
                    // Reproduce the insert case's final state outside timing.
                    fixture.insert(insert_target).expect("target setup failed");
                    fixture.check_mappings(background.iter().chain(std::iter::once(insert_target)));
                    let start = Instant::now();
                    let result = fixture.remove(black_box(insert_target));
                    elapsed += start.elapsed();
                    black_box(result).expect("region remove failed");
                    fixture.check_mappings(background);
                    fixture.check_region_pages(insert_target, false);
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
    // Select the operations before timing. The empty case calls the production
    // add/remove APIs directly, without mapping loops or clear/clear_iommu.
    if workload.zone_regions == 0 {
        zone_lifecycle_benches(
            c,
            "empty",
            Fixture::add_empty_zone,
            Fixture::remove_empty_zone,
            Fixture::check_empty,
        );
    } else {
        let mappings = workload.zone_mappings();
        let input = black_box(mappings.as_slice());
        zone_lifecycle_benches(
            c,
            &workload.zone_id(),
            |fixture| fixture.create_zone(input),
            Fixture::remove_zone,
            |fixture| fixture.check_zone(input),
        );
    }
}

fn zone_lifecycle_benches(
    c: &mut Criterion,
    case: &str,
    create: impl Fn(&Fixture) -> OpResult,
    remove: impl Fn(&Fixture) -> OpResult,
    check: impl Fn(&Fixture),
) {
    let fixture = Fixture::new();
    fixture.assert_all_frames_returned();
    for _ in 0..2 {
        create(&fixture).unwrap();
        check(&fixture);
        remove(&fixture).unwrap();
        fixture.check_removed();
    }
    fixture.assert_all_frames_returned();

    let fixture = black_box(&fixture);
    let mut group = c.benchmark_group("zone_memory");
    group.throughput(Throughput::Elements(1));
    group.bench_function(BenchmarkId::new("create", case), |b| {
        b.iter_custom(|rounds| {
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                let start = Instant::now();
                let result = create(fixture);
                elapsed += start.elapsed();
                black_box(result).expect("zone create failed");
                check(fixture);
                remove(fixture).expect("zone cleanup failed");
                fixture.check_removed();
            }
            elapsed
        });
    });
    group.bench_function(BenchmarkId::new("remove", case), |b| {
        b.iter_custom(|rounds| {
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                create(fixture).expect("zone setup failed");
                check(fixture);
                let start = Instant::now();
                let result = remove(fixture);
                elapsed += start.elapsed();
                black_box(result).expect("zone remove failed");
                fixture.check_removed();
            }
            elapsed
        });
    });
    group.finish();
    fixture.assert_all_frames_returned();
}

fn configured_criterion() -> Criterion {
    let workload = Workload::new();
    eprintln!(
        "Host software benchmark: prefill_regions={}, prefill_region_bytes={}, target_region_bytes={}; one timed region operation; zone_regions={}; hardware maintenance excluded",
        workload.prefill_regions,
        workload.prefill_pages * PAGE_SIZE,
        workload.target_pages * PAGE_SIZE,
        workload.zone_regions
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
