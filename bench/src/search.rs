use std::str;

use bstr::ByteSlice;
use criterion::Criterion;

use inputs::*;
use define;

// All english corpora.
const CORPORA_EN: &'static [(&'static str, &'static [u8])] = &[
    ("en-huge-ascii", SUBTITLE_EN_HUGE),
    ("en-small-ascii", SUBTITLE_EN_SMALL),
    ("en-tiny-ascii", SUBTITLE_EN_TINY),
];

pub fn find_iter(c: &mut Criterion) {
    define_find_iter(
        c, "find/rare", "en-huge-ascii",
        SUBTITLE_EN_HUGE, "Sherlock Holmes", 1,
    );
    define_find_iter(
        c, "find/verycommon1", "en-huge-ascii",
        SUBTITLE_EN_HUGE, " ", 76792,
    );
    define_find_iter(
        c, "find/verycommon2", "en-huge-ascii",
        SUBTITLE_EN_HUGE, "  ", 0,
    );

    define_find_iter(
        c, "find/rare", "en-small-ascii",
        SUBTITLE_EN_SMALL, "IM Pictures", 1,
    );
    define_find_iter(
        c, "find/verycommon1", "en-small-ascii",
        SUBTITLE_EN_SMALL, " ", 155,
    );
    define_find_iter(
        c, "find/verycommon2", "en-small-ascii",
        SUBTITLE_EN_SMALL, "  ", 0,
    );

    define_find_iter(
        c, "find/verycommon1", "en-tiny-ascii",
        SUBTITLE_EN_TINY, " ", 5,
    );
    define_find_iter(
        c, "find/verycommon2", "en-tiny-ascii",
        SUBTITLE_EN_TINY, "  ", 0,
    );

    define_find_iter(
        c, "find/pathological", "repeated-huge",
        REPEATED_RARE_HUGE, "abczdef", 0,
    );
    define_find_iter(
        c, "find/pathological", "repeated-small",
        REPEATED_RARE_SMALL, "abczdef", 0,
    );
}

pub fn rfind_iter(c: &mut Criterion) {
    define_rfind_iter(
        c, "rfind/rare", "en-huge-ascii",
        SUBTITLE_EN_HUGE, "Sherlock Holmes", 1,
    );
    define_rfind_iter(
        c, "rfind/verycommon1", "en-huge-ascii",
        SUBTITLE_EN_HUGE, " ", 76792,
    );
    define_rfind_iter(
        c, "rfind/verycommon2", "en-huge-ascii",
        SUBTITLE_EN_HUGE, "  ", 0,
    );

    define_rfind_iter(
        c, "rfind/rare", "en-small-ascii",
        SUBTITLE_EN_SMALL, "IM Pictures", 1,
    );
    define_rfind_iter(
        c, "rfind/verycommon1", "en-small-ascii",
        SUBTITLE_EN_SMALL, " ", 155,
    );
    define_rfind_iter(
        c, "rfind/verycommon2", "en-small-ascii",
        SUBTITLE_EN_SMALL, "  ", 0,
    );

    define_rfind_iter(
        c, "rfind/verycommon1", "en-tiny-ascii",
        SUBTITLE_EN_TINY, " ", 5,
    );
    define_rfind_iter(
        c, "rfind/verycommon2", "en-tiny-ascii",
        SUBTITLE_EN_TINY, "  ", 0,
    );

    define_rfind_iter(
        c, "rfind/pathological", "repeated-huge",
        REPEATED_RARE_HUGE, "abczdef", 0,
    );
    define_rfind_iter(
        c, "rfind/pathological", "repeated-small",
        REPEATED_RARE_SMALL, "abczdef", 0,
    );
}

pub fn find_char(c: &mut Criterion) {
    let corpus = str::from_utf8(SUBTITLE_EN_HUGE).unwrap();
    define(c, "bstr/find_char", "en-huge-ascii", corpus.as_bytes(), move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.find_char('γ'));
        });
    });

    define(c, "std/find_char", "en-huge-ascii", corpus.as_bytes(), move |b| {
        b.iter(|| {
            assert_eq!(None, corpus.find('γ'));
        });
    });
}

fn define_find_iter(
    c: &mut Criterion,
    group_name: &str,
    bench_name: &str,
    corpus: &'static [u8],
    needle: &'static str,
    expected: usize,
) {
    let corpus = str::from_utf8(corpus).unwrap();

    let name = format!("bstr/{}", group_name);
    define(c, &name, bench_name, corpus.as_bytes(), move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(expected, corpus.find_iter(needle).count());
        });
    });

    let name = format!("std/{}", group_name);
    define(c, &name, bench_name, corpus.as_bytes(), move |b| {
        b.iter(|| {
            assert_eq!(expected, corpus.matches(needle).count());
        });
    });
}

fn define_rfind_iter(
    c: &mut Criterion,
    group_name: &str,
    bench_name: &str,
    corpus: &'static [u8],
    needle: &'static str,
    expected: usize,
) {
    let corpus = str::from_utf8(corpus).unwrap();

    let name = format!("bstr/{}", group_name);
    define(c, &name, bench_name, corpus.as_bytes(), move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(expected, corpus.rfind_iter(needle).count());
        });
    });

    let name = format!("std/{}", group_name);
    define(c, &name, bench_name, corpus.as_bytes(), move |b| {
        b.iter(|| {
            assert_eq!(expected, corpus.rmatches(needle).count());
        });
    });
}
