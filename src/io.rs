/*!
Utilities for working with I/O using byte strings.

This module currently only exports a single trait, `BufReadExt`, which provides
facilities for conveniently and efficiently working with lines as byte strings.

More APIs may be added in the future.
*/

use std::io;

use ext_slice::ByteSlice;
use ext_vec::ByteVec;

/// An extention trait for
/// [`std::io::BufRead`](https://doc.rust-lang.org/std/io/trait.BufRead.html)
/// which provides convenience APIs for dealing with byte strings.
pub trait BufReadExt: io::BufRead {
    /// Returns an iterator over the lines of this reader, where each line
    /// is represented as a byte string.
    ///
    /// Each item yielded by this iterator is a `io::Result<Vec<u8>>`, where
    /// an error is yielded if there was a problem reading from the underlying
    /// reader.
    ///
    /// On success, the next line in the iterator is returned. The line does
    /// *not* contain a trailing `\n` or `\r\n`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::io;
    ///
    /// use bstr::io::BufReadExt;
    ///
    /// # fn example() -> Result<(), io::Error> {
    /// let cursor = io::Cursor::new(b"lorem\nipsum\r\ndolor");
    ///
    /// let mut lines = vec![];
    /// for result in cursor.byte_lines() {
    ///     let line = result?;
    ///     lines.push(line);
    /// }
    /// assert_eq!(lines.len(), 3);
    /// assert_eq!(lines[0], "lorem".as_bytes());
    /// assert_eq!(lines[1], "ipsum".as_bytes());
    /// assert_eq!(lines[2], "dolor".as_bytes());
    /// # Ok(()) }; example().unwrap()
    /// ```
    fn byte_lines(self) -> ByteLines<Self>
    where
        Self: Sized,
    {
        ByteLines { buf: self }
    }

    /// Executes the given closure on each line in the underlying reader.
    ///
    /// If the closure returns an error (or if the underlying reader returns an
    /// error), then iteration is stopped and the error is returned. If false
    /// is returned, then iteration is stopped and no error is returned.
    ///
    /// The closure given is called on exactly the same values as yielded by
    /// the [`byte_lines`](trait.BufReadExt.html#method.byte_lines)
    /// iterator. Namely, lines do _not_ contain trailing `\n` or `\r\n` bytes.
    ///
    /// This routine is useful for iterating over lines as quickly as
    /// possible. Namely, a single allocation is reused for each line.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::io;
    ///
    /// use bstr::io::BufReadExt;
    ///
    /// # fn example() -> Result<(), io::Error> {
    /// let cursor = io::Cursor::new(b"lorem\nipsum\r\ndolor");
    ///
    /// let mut lines = vec![];
    /// cursor.for_byte_line(|line| {
    ///     lines.push(line.to_vec());
    ///     Ok(true)
    /// })?;
    /// assert_eq!(lines.len(), 3);
    /// assert_eq!(lines[0], "lorem".as_bytes());
    /// assert_eq!(lines[1], "ipsum".as_bytes());
    /// assert_eq!(lines[2], "dolor".as_bytes());
    /// # Ok(()) }; example().unwrap()
    /// ```
    fn for_byte_line<F>(self, mut for_each_line: F) -> io::Result<()>
    where
        Self: Sized,
        F: FnMut(&[u8]) -> io::Result<bool>,
    {
        self.for_byte_line_with_terminator(|line| {
            for_each_line(&trim_slice(&line))
        })
    }

    /// Executes the given closure on each line in the underlying reader.
    ///
    /// If the closure returns an error (or if the underlying reader returns an
    /// error), then iteration is stopped and the error is returned. If false
    /// is returned, then iteration is stopped and no error is returned.
    ///
    /// Unlike
    /// [`for_byte_line`](trait.BufReadExt.html#method.for_byte_line),
    /// the lines given to the closure *do* include the line terminator, if one
    /// exists.
    ///
    /// This routine is useful for iterating over lines as quickly as
    /// possible. Namely, a single allocation is reused for each line.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::io;
    ///
    /// use bstr::io::BufReadExt;
    ///
    /// # fn example() -> Result<(), io::Error> {
    /// let cursor = io::Cursor::new(b"lorem\nipsum\r\ndolor");
    ///
    /// let mut lines = vec![];
    /// cursor.for_byte_line_with_terminator(|line| {
    ///     lines.push(line.to_vec());
    ///     Ok(true)
    /// })?;
    /// assert_eq!(lines.len(), 3);
    /// assert_eq!(lines[0], "lorem\n".as_bytes());
    /// assert_eq!(lines[1], "ipsum\r\n".as_bytes());
    /// assert_eq!(lines[2], "dolor".as_bytes());
    /// # Ok(()) }; example().unwrap()
    /// ```
    fn for_byte_line_with_terminator<F>(
        mut self,
        mut for_each_line: F,
    ) -> io::Result<()>
    where
        Self: Sized,
        F: FnMut(&[u8]) -> io::Result<bool>,
    {
        let mut bytes = vec![];
        let mut res = Ok(());
        let mut consumed = 0;
        'outer: loop {
            // Lend out complete line slices from our buffer
            {
                let mut buf = self.fill_buf()?;
                while let Some(index) = buf.find_byte(b'\n') {
                    let (line, rest) = buf.split_at(index + 1);
                    buf = rest;
                    consumed += line.len();
                    match for_each_line(&line) {
                        Ok(false) => break 'outer,
                        Err(err) => {
                            res = Err(err);
                            break 'outer;
                        }
                        _ => (),
                    }
                }

                // Copy the final line fragment to our local buffer. This saves
                // read_until() from re-scanning a buffer we know contains no
                // remaining newlines.
                bytes.extend_from_slice(&buf);
                consumed += buf.len();
            }

            self.consume(consumed);
            consumed = 0;

            // N.B. read_until uses a different version of memchr that may
            // be slower than the memchr crate that bstr uses. However, this
            // should only run for a fairly small number of lines, assuming a
            // decent buffer size.
            self.read_until(b'\n', &mut bytes)?;
            if bytes.is_empty() || !for_each_line(&bytes)? {
                break;
            }
            bytes.clear();
        }
        self.consume(consumed);
        res
    }
}

impl<B: io::BufRead> BufReadExt for B {}

/// An iterator over lines from an instance of
/// [`std::io::BufRead`](https://doc.rust-lang.org/std/io/trait.BufRead.html).
///
/// This iterator is generally created by calling the
/// [`byte_lines`](trait.BufReadExt.html#method.byte_lines)
/// method on the
/// [`BufReadExt`](trait.BufReadExt.html)
/// trait.
#[derive(Debug)]
pub struct ByteLines<B> {
    buf: B,
}

impl<B: io::BufRead> Iterator for ByteLines<B> {
    type Item = io::Result<Vec<u8>>;

    fn next(&mut self) -> Option<io::Result<Vec<u8>>> {
        let mut bytes = vec![];
        match self.buf.read_until(b'\n', &mut bytes) {
            Err(e) => Some(Err(e)),
            Ok(0) => None,
            Ok(_) => {
                trim_line(&mut bytes);
                Some(Ok(bytes))
            }
        }
    }
}

fn trim_slice(mut line: &[u8]) -> &[u8] {
    if line.last_byte() == Some(b'\n') {
        line = &line[..line.len() - 1];
        if line.last_byte() == Some(b'\r') {
            line = &line[..line.len() - 1];
        }
    }
    line
}

fn trim_line(line: &mut Vec<u8>) {
    if line.last_byte() == Some(b'\n') {
        line.pop_byte();
        if line.last_byte() == Some(b'\r') {
            line.pop_byte();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BufReadExt;
    use bstring::BString;

    fn collect_lines<B: AsRef<[u8]>>(slice: B) -> Vec<BString> {
        let mut lines = vec![];
        slice
            .as_ref()
            .for_byte_line(|line| {
                lines.push(BString::from(line.to_vec()));
                Ok(true)
            })
            .unwrap();
        lines
    }

    fn collect_lines_term<B: AsRef<[u8]>>(slice: B) -> Vec<BString> {
        let mut lines = vec![];
        slice
            .as_ref()
            .for_byte_line_with_terminator(|line| {
                lines.push(BString::from(line.to_vec()));
                Ok(true)
            })
            .unwrap();
        lines
    }

    #[test]
    fn lines_without_terminator() {
        assert_eq!(collect_lines(""), Vec::<BString>::new());

        assert_eq!(collect_lines("\n"), vec![""]);
        assert_eq!(collect_lines("\n\n"), vec!["", ""]);
        assert_eq!(collect_lines("a\nb\n"), vec!["a", "b"]);
        assert_eq!(collect_lines("a\nb"), vec!["a", "b"]);
        assert_eq!(collect_lines("abc\nxyz\n"), vec!["abc", "xyz"]);
        assert_eq!(collect_lines("abc\nxyz"), vec!["abc", "xyz"]);

        assert_eq!(collect_lines("\r\n"), vec![""]);
        assert_eq!(collect_lines("\r\n\r\n"), vec!["", ""]);
        assert_eq!(collect_lines("a\r\nb\r\n"), vec!["a", "b"]);
        assert_eq!(collect_lines("a\r\nb"), vec!["a", "b"]);
        assert_eq!(collect_lines("abc\r\nxyz\r\n"), vec!["abc", "xyz"]);
        assert_eq!(collect_lines("abc\r\nxyz"), vec!["abc", "xyz"]);

        assert_eq!(collect_lines("abc\rxyz"), vec!["abc\rxyz"]);
    }

    #[test]
    fn lines_with_terminator() {
        assert_eq!(collect_lines_term(""), Vec::<BString>::new());

        assert_eq!(collect_lines_term("\n"), vec!["\n"]);
        assert_eq!(collect_lines_term("\n\n"), vec!["\n", "\n"]);
        assert_eq!(collect_lines_term("a\nb\n"), vec!["a\n", "b\n"]);
        assert_eq!(collect_lines_term("a\nb"), vec!["a\n", "b"]);
        assert_eq!(collect_lines_term("abc\nxyz\n"), vec!["abc\n", "xyz\n"]);
        assert_eq!(collect_lines_term("abc\nxyz"), vec!["abc\n", "xyz"]);

        assert_eq!(collect_lines_term("\r\n"), vec!["\r\n"]);
        assert_eq!(collect_lines_term("\r\n\r\n"), vec!["\r\n", "\r\n"]);
        assert_eq!(collect_lines_term("a\r\nb\r\n"), vec!["a\r\n", "b\r\n"]);
        assert_eq!(collect_lines_term("a\r\nb"), vec!["a\r\n", "b"]);
        assert_eq!(
            collect_lines_term("abc\r\nxyz\r\n"),
            vec!["abc\r\n", "xyz\r\n"]
        );
        assert_eq!(collect_lines_term("abc\r\nxyz"), vec!["abc\r\n", "xyz"]);

        assert_eq!(collect_lines_term("abc\rxyz"), vec!["abc\rxyz"]);
    }
}
