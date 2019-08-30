use std::str;

use bstr::ByteSlice;
use criterion::Criterion;

use define;
use inputs::*;

pub fn find_iter(c: &mut Criterion) {
    define_find_iter(
        c,
        "find/rare",
        "en-huge-ascii",
        SUBTITLE_EN_HUGE,
        "Sherlock Holmes",
        1,
    );
    define_find_iter(
        c,
        "find/verycommon1",
        "en-huge-ascii",
        SUBTITLE_EN_HUGE,
        " ",
        76792,
    );
    define_find_iter(
        c,
        "find/verycommon2",
        "en-huge-ascii",
        SUBTITLE_EN_HUGE,
        "  ",
        0,
    );

    define_find_iter(
        c,
        "find/rare",
        "en-small-ascii",
        SUBTITLE_EN_SMALL,
        "IM Pictures",
        1,
    );
    define_find_iter(
        c,
        "find/verycommon1",
        "en-small-ascii",
        SUBTITLE_EN_SMALL,
        " ",
        155,
    );
    define_find_iter(
        c,
        "find/verycommon2",
        "en-small-ascii",
        SUBTITLE_EN_SMALL,
        "  ",
        0,
    );

    define_find_iter(
        c,
        "find/verycommon1",
        "en-tiny-ascii",
        SUBTITLE_EN_TINY,
        " ",
        5,
    );
    define_find_iter(
        c,
        "find/verycommon2",
        "en-tiny-ascii",
        SUBTITLE_EN_TINY,
        "  ",
        0,
    );

    define_find_iter(
        c,
        "find/pathological",
        "repeated-huge",
        REPEATED_RARE_HUGE,
        "abczdef",
        0,
    );
    define_find_iter(
        c,
        "find/pathological",
        "repeated-small",
        REPEATED_RARE_SMALL,
        "abczdef",
        0,
    );
}

pub fn rfind_iter(c: &mut Criterion) {
    define_rfind_iter(
        c,
        "rfind/rare",
        "en-huge-ascii",
        SUBTITLE_EN_HUGE,
        "Sherlock Holmes",
        1,
    );
    define_rfind_iter(
        c,
        "rfind/verycommon1",
        "en-huge-ascii",
        SUBTITLE_EN_HUGE,
        " ",
        76792,
    );
    define_rfind_iter(
        c,
        "rfind/verycommon2",
        "en-huge-ascii",
        SUBTITLE_EN_HUGE,
        "  ",
        0,
    );

    define_rfind_iter(
        c,
        "rfind/rare",
        "en-small-ascii",
        SUBTITLE_EN_SMALL,
        "IM Pictures",
        1,
    );
    define_rfind_iter(
        c,
        "rfind/verycommon1",
        "en-small-ascii",
        SUBTITLE_EN_SMALL,
        " ",
        155,
    );
    define_rfind_iter(
        c,
        "rfind/verycommon2",
        "en-small-ascii",
        SUBTITLE_EN_SMALL,
        "  ",
        0,
    );

    define_rfind_iter(
        c,
        "rfind/verycommon1",
        "en-tiny-ascii",
        SUBTITLE_EN_TINY,
        " ",
        5,
    );
    define_rfind_iter(
        c,
        "rfind/verycommon2",
        "en-tiny-ascii",
        SUBTITLE_EN_TINY,
        "  ",
        0,
    );

    define_rfind_iter(
        c,
        "rfind/pathological",
        "repeated-huge",
        REPEATED_RARE_HUGE,
        "abczdef",
        0,
    );
    define_rfind_iter(
        c,
        "rfind/pathological",
        "repeated-small",
        REPEATED_RARE_SMALL,
        "abczdef",
        0,
    );
}

pub fn find_char(c: &mut Criterion) {
    let corpus = str::from_utf8(SUBTITLE_EN_HUGE).unwrap();
    define(
        c,
        "bstr/find_char",
        "en-huge-ascii",
        corpus.as_bytes(),
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(None, corpus.find_char('γ'));
            });
        },
    );

    define(c, "std/find_char", "en-huge-ascii", corpus.as_bytes(), move |b| {
        b.iter(|| {
            assert_eq!(None, corpus.find('γ'));
        });
    });
}

pub fn find_byteset(c: &mut Criterion) {
    let corpus = SUBTITLE_EN_SMALL;
    define(c, "bstr/find_byteset/1", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.find_byteset(b"\0"));
        });
    });
    define(c, "bstr/find_byteset/2", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.find_byteset(b"\0\xff"));
        });
    });
    define(c, "bstr/find_byteset/3", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.find_byteset(b"\0\xff\xee"));
        });
    });
    define(c, "bstr/find_byteset/4", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.find_byteset(b"\0\xff\xee\xdd"));
        });
    });
    define(c, "bstr/find_byteset/10", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.find_byteset(b"0123456789"));
        });
    });

    define(c, "bstr/rfind_byteset/1", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.rfind_byteset(b"\0"));
        });
    });
    define(c, "bstr/rfind_byteset/2", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.rfind_byteset(b"\0\xff"));
        });
    });
    define(c, "bstr/rfind_byteset/3", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.rfind_byteset(b"\0\xff\xee"));
        });
    });
    define(c, "bstr/rfind_byteset/4", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.rfind_byteset(b"\0\xff\xee\xdd"));
        });
    });
    define(c, "bstr/rfind_byteset/10", "en-small-ascii", corpus, move |b| {
        let corpus = corpus.as_bytes();
        b.iter(|| {
            assert_eq!(None, corpus.rfind_byteset(b"0123456789"));
        });
    });
}

pub fn find_not_byteset(c: &mut Criterion) {
    let corpus = REPEATED_RARE_SMALL;
    define(
        c,
        "bstr/find_not_byteset/1",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(Some(1000), corpus.find_not_byteset(b"z"));
            })
        },
    );
    define(
        c,
        "bstr/find_not_byteset/2",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(Some(1000), corpus.find_not_byteset(b"zy"));
            });
        },
    );
    define(
        c,
        "bstr/find_not_byteset/3",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(Some(1000), corpus.find_not_byteset(b"zyx"));
            });
        },
    );
    define(
        c,
        "bstr/find_not_byteset/4",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(Some(1000), corpus.find_not_byteset(b"zyxw"));
            });
        },
    );
    define(
        c,
        "bstr/find_not_byteset/10",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(Some(1000), corpus.find_not_byteset(b"zyxwv12345"));
            });
        },
    );

    define(
        c,
        "bstr/rfind_not_byteset/1",
        "repeated-rare-small",
        corpus,
        move |b| {
            // This file ends in \n, breaking our benchmark.... TODO find a
            // better dataset...
            let corpus = &corpus.as_bytes()[..(corpus.len() - 1)];
            b.iter(|| {
                assert_eq!(None, corpus.rfind_not_byteset(b"z"));
            });
        },
    );
    define(
        c,
        "bstr/rfind_not_byteset/2",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(None, corpus.rfind_not_byteset(b"z\n"));
            });
        },
    );
    define(
        c,
        "bstr/rfind_not_byteset/3",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(None, corpus.rfind_not_byteset(b"zy\n"));
            });
        },
    );
    define(
        c,
        "bstr/rfind_not_byteset/4",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(None, corpus.rfind_not_byteset(b"zyx\n"));
            });
        },
    );
    define(
        c,
        "bstr/rfind_not_byteset/10",
        "repeated-rare-small",
        corpus,
        move |b| {
            let corpus = corpus.as_bytes();
            b.iter(|| {
                assert_eq!(None, corpus.rfind_not_byteset(b"zyxwv1234\n"));
            });
        },
    );
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
