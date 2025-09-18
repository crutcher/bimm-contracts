use bimm_contracts::slots::slot_contracts::{SlotDimMatcher, SlotShapeContract};
use bimm_contracts::slots::slot_expressions::SlotDimExpr;
use bimm_contracts::{DimExpr, DimMatcher, ShapeContract, run_periodically};
use criterion::{Criterion, criterion_group, criterion_main};

static PATTERN: ShapeContract = ShapeContract::new(&[
    DimMatcher::any(),
    DimMatcher::expr(DimExpr::Param("b")),
    DimMatcher::ellipsis(),
    DimMatcher::expr(DimExpr::Prod(&[DimExpr::Param("h"), DimExpr::Param("p")])),
    DimMatcher::expr(DimExpr::Prod(&[DimExpr::Param("w"), DimExpr::Param("p")])),
    DimMatcher::expr(DimExpr::Pow(&DimExpr::Param("z"), 3)),
    DimMatcher::expr(DimExpr::Param("c")),
]);

static BATCH: usize = 2;
static HEIGHT: usize = 3;
static WIDTH: usize = 2;
static PADDING: usize = 4;
static CHANNELS: usize = 5;
static COLOR: usize = 4;

fn bench_slot_unpack_shape(c: &mut Criterion) {
    let shape = [
        12,
        BATCH,
        1,
        2,
        3,
        HEIGHT * PADDING,
        WIDTH * PADDING,
        COLOR * COLOR * COLOR,
        CHANNELS,
    ];

    static S_PATTERN: SlotShapeContract = SlotShapeContract {
        index: &["batch", "height", "width", "padding", "color", "channels"],
        terms: &[
            SlotDimMatcher::any(),
            SlotDimMatcher::expr(SlotDimExpr::Param { id: 0 }),
            SlotDimMatcher::ellipsis(),
            SlotDimMatcher::expr(SlotDimExpr::Prod {
                children: &[SlotDimExpr::Param { id: 1 }, SlotDimExpr::Param { id: 3 }],
            }),
            SlotDimMatcher::expr(SlotDimExpr::Prod {
                children: &[SlotDimExpr::Param { id: 2 }, SlotDimExpr::Param { id: 3 }],
            }),
            SlotDimMatcher::expr(SlotDimExpr::Pow {
                base: &SlotDimExpr::Param { id: 4 },
                exp: 3,
            }),
            SlotDimMatcher::expr(SlotDimExpr::Param { id: 5 }),
        ],
        ellipsis_pos: Some(2),
    };

    let bindings = [
        None,
        None,
        None,
        Some(PADDING as isize),
        None,
        Some(CHANNELS as isize),
    ];

    // thread_local! { static SCRATCH: RefCell<Vec<Option<isize>>> = RefCell::new(vec![None; 6]); }
    c.bench_function("unpack_shape w/slots", |b| {
        b.iter(|| {
            let mut env = bindings;
            S_PATTERN._resolve(&shape, &mut env).unwrap()
        })
    });
}

fn bench_unpack_shape(c: &mut Criterion) {
    let shape = [
        12,
        BATCH,
        1,
        2,
        3,
        HEIGHT * PADDING,
        WIDTH * PADDING,
        COLOR * COLOR * COLOR,
        CHANNELS,
    ];
    let env = [("p", PADDING), ("c", CHANNELS)];

    c.bench_function("unpack_shape", |b| {
        b.iter(|| {
            let [b, h, w, c] = PATTERN.unpack_shape(&shape, &["b", "h", "w", "z"], &env);

            assert_eq!(b, BATCH);
            assert_eq!(h, HEIGHT);
            assert_eq!(w, WIDTH);
            assert_eq!(c, COLOR);
        })
    });
}

fn bench_assert_shape(c: &mut Criterion) {
    let shape = [
        12,
        BATCH,
        1,
        2,
        3,
        HEIGHT * PADDING,
        WIDTH * PADDING,
        COLOR * COLOR * COLOR,
        CHANNELS,
    ];
    let env = [("p", PADDING), ("c", CHANNELS)];

    c.bench_function("assert_shape", |b| {
        b.iter(|| {
            PATTERN.assert_shape(&shape, &env);
        })
    });
}

fn bench_assert_shape_every_nth(c: &mut Criterion) {
    let shape = [
        12,
        BATCH,
        1,
        2,
        3,
        HEIGHT * PADDING,
        WIDTH * PADDING,
        COLOR * COLOR * COLOR,
        CHANNELS,
    ];
    let env = [("p", PADDING), ("c", CHANNELS)];

    let mut group = c.benchmark_group("assert_shape_every_nth");
    group.warm_up_time(std::time::Duration::from_nanos(1));

    group.bench_function("assert_shape_every_nth", |b| {
        b.iter(|| {
            run_periodically!(PATTERN.assert_shape(&shape, &env));
        })
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_slot_unpack_shape,
    bench_unpack_shape,
    bench_assert_shape,
    bench_assert_shape_every_nth
);
criterion_main!(benches);
