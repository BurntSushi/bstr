pub use self::grapheme::{Graphemes, GraphemeIndices, decode_grapheme};
pub use self::sentence::{Sentences, SentenceIndices};
pub use self::whitespace::{whitespace_len_fwd, whitespace_len_rev};
pub use self::word::{
    Words, WordIndices, WordsWithBreaks, WordsWithBreakIndices,
};

mod fsm;
mod grapheme;
mod sentence;
mod whitespace;
mod word;
