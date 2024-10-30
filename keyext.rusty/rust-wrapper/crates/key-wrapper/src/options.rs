/// Options for wrapper.
#[derive(Debug, Clone)]
pub struct Options {
    /// Where to write output if any.
    pub output_file: Option<OutputFile>,
    /// Whether to pretty print the output.
    pub pretty_print: bool,
}

/// Where to write the output.
#[derive(Debug, Clone)]
pub enum OutputFile {
    /// Write to a file at a path.
    File(String),
    /// Standard output.
    Stdout,
}
