mod varint_write;

use criterion::measurement::WallTime;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, BenchmarkId, Criterion};
use std::hint::black_box;
use yarms_protocol::types::VarInt;
use yarms_protocol::util;
use yarms_protocol::util::LebFlow;

#[inline]
fn byte_by_byte_read(input: &[u8; 5]) -> yarms_protocol::Result<VarInt> {
    let mut pos = 0;
    let mut value = 0;

    for b in input {
        if util::var_int_advance_read(*b, &mut pos, &mut value)? == LebFlow::Done {
            return Ok(VarInt::from(value));
        }
    }

    unreachable!()
}

fn input(input: [u8; 5]) -> (BenchmarkId, [u8; 5]) {
    (
        BenchmarkId::new("var_int_read", format!("{:?}", &input)),
        input,
    )
}

fn bench_input(group: &mut BenchmarkGroup<WallTime>, id: BenchmarkId, input: [u8; 5]) {
    group.bench_with_input(id, &input, |b, i| {
        b.iter(|| util::var_int_read(black_box(i)))
    });
}

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("VarInt Read (full)");

    let (id_1, input_1) = input([0u8; 5]);
    let (id_2, input_2) = input([0xFF, 0x7F, 0, 0, 0]);
    let (id_3, input_3) = input([0xFF, 0xFF, 0xFF, 0x7F, 0x0]);

    bench_input(&mut group, id_1.clone(), input_1);
    bench_input(&mut group, id_2.clone(), input_2);
    bench_input(&mut group, id_3.clone(), input_3);
    group.finish();

    let mut group_2 = c.benchmark_group("VarInt Read (byte-by-byte)");
    group_2.bench_with_input(id_1.clone(), &input_1, |b, i| {
        b.iter(|| byte_by_byte_read(black_box(i)))
    });

    group_2.bench_with_input(id_2.clone(), &input_2, |b, i| {
        b.iter(|| byte_by_byte_read(black_box(i)))
    });

    group_2.bench_with_input(id_3.clone(), &input_3, |b, i| {
        b.iter(|| byte_by_byte_read(black_box(i)))
    });
    group_2.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
