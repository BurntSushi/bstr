extern crate bstr;

use std::error::Error;
use std::io::{self, Write};

use bstr::BString;
use bstr::io::BufReadExt;

fn main() -> Result<(), Box<Error>> {
    let stdin = io::stdin();
    let mut stdout = io::BufWriter::new(io::stdout());

    let mut upper = BString::new();
    stdin.lock().for_byte_line_with_terminator(|line| {
        upper.clear();
        line.to_uppercase_into(&mut upper);
        stdout.write_all(upper.as_bytes())?;
        Ok(true)
    })?;
    Ok(())
}
