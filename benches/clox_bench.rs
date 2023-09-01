use criterion::{black_box, criterion_group, criterion_main, Criterion};

use lox::clox;

pub fn criterion_benchmark(c: &mut Criterion) {
    let heap = clox::Heap::new();
    let mut vm = clox::Vm::new(&heap);
    let mut runner = vm.compile("var x=0;").unwrap();
    c.bench_function("noop", |b| {
        b.iter(|| {
            black_box(&mut runner).run().unwrap();
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
