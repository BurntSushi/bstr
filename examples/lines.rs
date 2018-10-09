extern crate bstr;

use std::error::Error;
use std::io::{self, Write};

use bstr::io::BufReadExt;

fn main() -> Result<(), Box<Error>> {
    let stdin = io::stdin();
    let mut stdout = io::BufWriter::new(io::stdout());

    stdin.lock().for_byte_line_with_terminator(|line| {
        if line.contains("Dimension") {
            stdout.write_all(line.as_bytes())?;
        }
        Ok(true)
    })?;
    Ok(())
}
