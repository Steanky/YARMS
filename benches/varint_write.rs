use bytes::BufMut;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;
use yarms_protocol::util;
use yarms_protocol::util::LebFlow;

#[inline]
fn byte_by_byte_write<B: BufMut>(mut input: i32, output: &mut B) -> usize {
    let mut out = 0;
    let mut cnt = 0;

    loop {
        let res = util::var_int_advance_write(&mut out, &mut input);
        output.put_u8(out);
        cnt += 1;

        if res == LebFlow::Done {
            return cnt;
        }
    }
}

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("VarInt Write (full)");

    let id_1 = BenchmarkId::new("var_int_write", format!("{:?}", 0));
    let id_2 = BenchmarkId::new("var_int_write", format!("{:?}", 65536));
    let id_3 = BenchmarkId::new("var_int_write", format!("{:?}", i32::MIN));

    group.bench_with_input(id_1.clone(), &0, |b, i| {
        let mut buf = [0u8; 5];

        b.iter(|| util::var_int_write_array(black_box(*i), black_box(&mut buf)))
    });

    group.bench_with_input(id_2.clone(), &65536, |b, i| {
        let mut buf = [0u8; 5];

        b.iter(|| util::var_int_write_array(black_box(*i), black_box(&mut buf)))
    });

    group.bench_with_input(id_3.clone(), &i32::MIN, |b, i| {
        let mut buf = [0u8; 5];

        b.iter(|| util::var_int_write_array(black_box(*i), black_box(&mut buf)))
    });

    group.finish();

    let mut group = c.benchmark_group("VarInt Write (byte-by-byte)");
    group.bench_with_input(id_1.clone(), &0, |b, i| {
        let mut buf = [0u8; 5];

        b.iter(|| byte_by_byte_write(black_box(*i), black_box(&mut &mut buf[..])))
    });

    group.bench_with_input(id_2.clone(), &65536, |b, i| {
        let mut buf = [0u8; 5];

        b.iter(|| byte_by_byte_write(black_box(*i), black_box(&mut &mut buf[..])))
    });

    group.bench_with_input(id_3.clone(), &i32::MIN, |b, i| {
        let mut buf = [0u8; 5];

        b.iter(|| byte_by_byte_write(black_box(*i), black_box(&mut &mut buf[..])))
    });

    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
