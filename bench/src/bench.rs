#[macro_use]
extern crate criterion;
extern crate bstr;
extern crate unicode_segmentation;

use bstr::{ByteSlice, B};
use criterion::{Bencher, Criterion, Throughput};

use inputs::*;

mod inputs;
mod search;

// All benchmark corpora up to and including "huge" inputs.
//
// "huge" inputs are about 500KB. "small" inputs are about 1KB. "tiny" inputs
// are under 100 bytes.
const CORPORA_HUGE: &'static [(&'static str, &'static [u8])] = &[
    ("en-huge-ascii", SUBTITLE_EN_HUGE),
    ("en-small-ascii", SUBTITLE_EN_SMALL),
    ("en-tiny-ascii", SUBTITLE_EN_TINY),
    ("ru-huge-utf8", SUBTITLE_RU_HUGE),
    ("ru-small-utf8", SUBTITLE_RU_SMALL),
    ("ru-tiny-utf8", SUBTITLE_RU_TINY),
    ("zh-huge-utf8", SUBTITLE_ZH_HUGE),
    ("zh-small-utf8", SUBTITLE_ZH_SMALL),
    ("zh-tiny-utf8", SUBTITLE_ZH_TINY),
];

// All benchmark corpora up to and including "small" inputs. This does not
// include huge inputs. This is useful for benchmarks that take longer, or if
// there isn't useful to benchmark larger inputs.
//
// "huge" inputs are about 500KB. "small" inputs are about 1KB. "tiny" inputs
// are under 100 bytes.
const CORPORA_SMALL: &'static [(&'static str, &'static [u8])] = &[
    ("en-small-ascii", SUBTITLE_EN_SMALL),
    ("en-tiny-ascii", SUBTITLE_EN_TINY),
    ("ru-small-utf8", SUBTITLE_RU_SMALL),
    ("ru-tiny-utf8", SUBTITLE_RU_TINY),
    ("zh-small-utf8", SUBTITLE_ZH_SMALL),
    ("zh-tiny-utf8", SUBTITLE_ZH_TINY),
];

fn is_ascii(c: &mut Criterion) {
    let corpus = SHERLOCK_HUGE;
    define(c, "is_ascii", "huge-ascii", corpus, move |b| {
        b.iter(|| {
            assert!(corpus.is_ascii());
        });
    });

    let corpus = SHERLOCK_SMALL;
    define(c, "is_ascii", "small-ascii", corpus, move |b| {
        b.iter(|| {
            assert!(corpus.is_ascii());
        });
    });

    let corpus = SHERLOCK_TINY;
    define(c, "is_ascii", "tiny-ascii", corpus, move |b| {
        b.iter(|| {
            assert!(corpus.is_ascii());
        });
    });

    let corpus = EMPTY;
    define(c, "is_ascii", "empty-ascii", corpus, move |b| {
        b.iter(|| {
            assert!(corpus.is_ascii());
        });
    });

    let corpus = "abcdefghijklm☃abcdefghijklmnopqrstuvwxyz".as_bytes();
    define(c, "is_ascii", "tiny-non-ascii", corpus, move |b| {
        b.iter(|| {
            assert!(!corpus.is_ascii());
        });
    });
}

fn to_str(c: &mut Criterion) {
    // benchmark our impl
    for &(name, corpus) in CORPORA_HUGE {
        define(c, "bstr/to_str", name, corpus, move |b| {
            b.iter(|| {
                assert!(corpus.to_str().is_ok());
            });
        });
    }
    // benchmark std's impl
    for &(name, corpus) in CORPORA_HUGE {
        define(c, "std/to_str", name, corpus, move |b| {
            use std::str;

            b.iter(|| {
                assert!(str::from_utf8(corpus).is_ok());
            });
        });
    }
}

fn to_str_lossy_valid(c: &mut Criterion) {
    // benchmark our impl
    for &(name, corpus) in CORPORA_HUGE {
        define(c, "bstr/to_str_lossy_valid", name, corpus, move |b| {
            b.iter(|| {
                assert!(corpus.to_str_lossy().len() > 0);
            });
        });
    }
    // benchmark std's impl
    for &(name, corpus) in CORPORA_HUGE {
        define(c, "std/to_str_lossy_valid", name, corpus, move |b| {
            b.iter(|| {
                assert!(String::from_utf8_lossy(corpus).len() > 0);
            });
        });
    }
}

fn trim(c: &mut Criterion) {
    let corpus = "\u{2007}\t\n\u{200a}foo\tbar\t\t\t\t\n   \t\u{2002}";

    // benchmark our impl
    define(c, "bstr/trim", "tiny", corpus.as_bytes(), move |b| {
        b.iter(|| {
            assert_eq!("foo\tbar".as_bytes(), B(corpus).trim());
        });
    });

    // benchmark std's impl
    define(c, "std/trim", "tiny", corpus.as_bytes(), move |b| {
        b.iter(|| {
            assert_eq!("foo\tbar", corpus.trim());
        });
    });
}

fn chars(c: &mut Criterion) {
    // benchmark our impl
    for &(name, corpus) in CORPORA_HUGE {
        define(c, "bstr/chars", name, corpus, move |b| {
            b.iter(|| {
                let mut count = 0;
                for ch in corpus.chars() {
                    count += ch.len_utf8();
                }
                assert!(count > 0);
            });
        });
    }
    // benchmark std's impl
    for &(name, corpus) in CORPORA_HUGE {
        define(c, "std/chars", name, corpus, move |b| {
            use std::str;

            let corpus = str::from_utf8(corpus).unwrap();
            b.iter(|| {
                let mut count = 0;
                for ch in corpus.chars() {
                    count += ch.len_utf8();
                }
                assert!(count > 0);
            });
        });
    }
}

fn graphemes(c: &mut Criterion) {
    // benchmark our impl
    for &(name, corpus) in CORPORA_SMALL {
        define(c, "bstr/graphemes", name, corpus, move |b| {
            b.iter(|| {
                let mut count = 0;
                for g in corpus.graphemes() {
                    count += g.len();
                }
                assert!(count > 0);
            });
        });
    }
    // benchmark unicode-segmentation impl
    for &(name, corpus) in CORPORA_SMALL {
        define(c, "unicode-segmentation/graphemes", name, corpus, move |b| {
            use std::str;
            use unicode_segmentation::UnicodeSegmentation;

            let corpus = str::from_utf8(corpus).unwrap();
            b.iter(|| {
                let mut count = 0;
                for g in corpus.graphemes(true) {
                    count += g.len();
                }
                assert!(count > 0);
            });
        });
    }
}

fn words(c: &mut Criterion) {
    // benchmark our impl
    for &(name, corpus) in CORPORA_SMALL {
        define(c, "bstr/words", name, corpus, move |b| {
            b.iter(|| {
                let mut count = 0;
                for g in corpus.words() {
                    count += g.len();
                }
                assert!(count > 0);
            });
        });
    }
    // benchmark unicode-segmentation impl
    for &(name, corpus) in CORPORA_SMALL {
        define(c, "unicode-segmentation/words", name, corpus, move |b| {
            use std::str;
            use unicode_segmentation::UnicodeSegmentation;

            let corpus = str::from_utf8(corpus).unwrap();
            b.iter(|| {
                let mut count = 0;
                for g in corpus.unicode_words() {
                    count += g.len();
                }
                assert!(count > 0);
            });
        });
    }
}

fn sentences(c: &mut Criterion) {
    // benchmark our impl
    for &(name, corpus) in CORPORA_SMALL {
        define(c, "bstr/sentences", name, corpus, move |b| {
            b.iter(|| {
                let mut count = 0;
                for g in corpus.sentences() {
                    count += g.len();
                }
                assert!(count > 0);
            });
        });
    }
}

fn byte_lines(c: &mut Criterion) {
    use bstr::io::BufReadExt;

    let corpus = SUBTITLE_EN_HUGE;
    define(c, "bstr/for_byte_line", "ascii", corpus, move |b| {
        b.iter(|| {
            let mut count = 0;
            corpus
                .for_byte_line(|line| {
                    count += line.len();
                    Ok(true)
                })
                .unwrap();
            assert!(count > 0);
        });
    });
}

fn define(
    c: &mut Criterion,
    group_name: &str,
    bench_name: &str,
    corpus: &[u8],
    bench: impl FnMut(&mut Bencher) + 'static,
) {
    let mut group = c.benchmark_group(group_name);
    group.throughput(Throughput::Bytes(corpus.len() as u64));
    group.bench_function(bench_name, bench);
    group.finish();
}

criterion_group!(g1, is_ascii);
criterion_group!(g2, to_str);
criterion_group!(g3, to_str_lossy_valid);
criterion_group!(g4, trim);
criterion_group!(g5, chars);
criterion_group!(g6, graphemes);
criterion_group!(g7, words);
criterion_group!(g8, sentences);
criterion_group!(g9, byte_lines);
criterion_group!(g10, search::find_iter);
criterion_group!(g11, search::rfind_iter);
criterion_group!(g12, search::find_char);
criterion_group!(g13, search::find_byteset);
criterion_group!(g14, search::find_not_byteset);
criterion_main!(g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14);
