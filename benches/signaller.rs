use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("send+recv");

    let id_1 = BenchmarkId::new("signal_send_recv_sync", "");
    let id_2 = BenchmarkId::new("yarms_oneshot", "42");
    let id_3 = BenchmarkId::new("tokio_oneshot", "42");

    let id_4 = BenchmarkId::new("yarms_oneshot_await", "42");
    let id_5 = BenchmarkId::new("tokio_oneshot_await", "42");

    group.bench_function(id_1, |b| {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .expect("couldn't construct Tokio runtime");

        b.to_async(runtime).iter(|| async move {
            let (send, recv) = black_box(yarms_util_future::signal::channel());

            black_box(send.signal());
            black_box(recv.await)
        })
    });

    group.bench_function(id_2, |b| {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .expect("couldn't construct Tokio runtime");

        b.to_async(runtime).iter(|| async move {
            let (send, recv) = black_box(yarms_util_future::oneshot::channel());

            send.signal(black_box(42));
            recv.await
        })
    });

    group.bench_function(id_3, |b| {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .expect("couldn't construct Tokio runtime");

        b.to_async(runtime).iter(|| async move {
            let (send, recv) = black_box(tokio::sync::oneshot::channel());

            let _ = send.send(black_box(42));
            recv.await
        })
    });

    group.bench_function(id_4, |b| {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .expect("couldn't construct Tokio runtime");

        b.to_async(runtime).iter(|| async move {
            let (send, recv) = black_box(yarms_util_future::oneshot::channel());

            tokio::task::spawn(async move {
                send.signal(black_box(42));
            });

            recv.await
        })
    });

    group.bench_function(id_5, |b| {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .expect("couldn't construct Tokio runtime");

        b.to_async(runtime).iter(|| async move {
            let (send, recv) = black_box(tokio::sync::oneshot::channel());

            tokio::task::spawn(async move {
                let _ = send.send(black_box(42));
            });

            recv.await
        })
    });
}

criterion_group!(benches, bench);
criterion_main!(benches);
