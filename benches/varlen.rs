use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;
use yarms_protocol::util;

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("Compute VarInt length");

    let random_input: Vec<i32> = vec![
        0b11000110001010001111100110011101_u32 as i32,
        0b00010001100100111001101100101001_u32 as i32,
        0b10111010101001000010010011000100_u32 as i32,
        0b00111111011111001001010110100110_u32 as i32,
        0b10001111011001001100011000110001_u32 as i32,
        0b11010111010011111000010100110001_u32 as i32,
        0b10110011111110101111010001001101_u32 as i32,
        0b01010000111111000101010110011111_u32 as i32,
        0b10011011001100000011101111100110_u32 as i32,
        0b10111000001000100101001100111000_u32 as i32,
        0b01000011110100110100001100101110_u32 as i32,
        0b10000100011100111110111011000010_u32 as i32,
        0b11011011001000101001001011111100_u32 as i32,
        0b11010010100011111100111111001100_u32 as i32,
        0b00011001010100001000010010001110_u32 as i32,
        0b00011010100010100100010010100000_u32 as i32,
        0b11100010111011100111001000101110_u32 as i32,
        0b11001001110010111010110111101010_u32 as i32,
        0b00101011010000100011101101000100_u32 as i32,
    ];

    let id_1 = BenchmarkId::new("var_int_length", "random");
    group.bench_with_input(id_1.clone(), &random_input, |b, i| {
        b.iter(|| {
            for sample in i {
                black_box(util::var_int_len(black_box(*sample)));
            }
        })
    });
    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
