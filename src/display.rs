use std::{
    borrow::Cow,
    fmt::Display,
    io::{self, Write},
    str,
};

use indexmap::IndexMap;
use qname::QName;
use unic_ucd::GeneralCategory;

use crate::{
    document::{Declaration, Document},
    key::DocKey,
    value::{ElementValue, NodeValue},
    Node,
};

pub(crate) trait Print<Config, Context = ()> {
    fn print(&self, f: &mut dyn Write, config: &Config, context: &Context) -> std::io::Result<()>;
}

#[derive(Debug, Clone, Default)]
pub struct Config {
    pub(crate) is_pretty: bool,
    pub(crate) indent: usize,
    pub(crate) end_pad: usize,
    pub(crate) max_line_length: usize,
    pub(crate) entity_mode: EntityMode,
    pub(crate) indent_text_nodes: bool,
    pub(crate) tight: bool,
}

impl Config {
    pub fn default_pretty() -> Self {
        Config {
            is_pretty: true,
            indent: 2,
            end_pad: 1,
            max_line_length: 120,
            entity_mode: EntityMode::Standard,
            indent_text_nodes: true,
            tight: false,
        }
    }

    pub fn indent(mut self, indent: usize) -> Self {
        self.indent = indent;
        self
    }

    pub fn end_pad(mut self, end_pad: usize) -> Self {
        self.end_pad = end_pad;
        self
    }

    pub fn max_line_length(mut self, max_line_length: usize) -> Self {
        self.max_line_length = max_line_length;
        self
    }

    pub fn entity_mode(mut self, entity_mode: EntityMode) -> Self {
        self.entity_mode = entity_mode;
        self
    }

    pub fn indent_text_nodes(mut self, indent_text_nodes: bool) -> Self {
        self.indent_text_nodes = indent_text_nodes;
        self
    }

    /// Enables tight mode: an element and its entire subtree are collapsed onto a single line
    /// when the result fits within `max_line_length`, including elements that contain child
    /// elements (e.g. `<li><a href="...">Earth</a></li>`). Without this, only text-only
    /// content is kept inline and child elements always nest onto their own lines.
    pub fn tight(mut self) -> Self {
        self.tight = true;
        self
    }
}

#[derive(Debug, Clone)]
pub(crate) struct State<'a> {
    pub is_pretty: bool,
    pub indent: usize,
    pub key: DocKey,
    pub doc: &'a Document,
}

impl<'a> State<'a> {
    pub(crate) fn new(document: &'a Document, is_pretty: bool) -> Self {
        Self {
            is_pretty,
            indent: 0,
            doc: document,
            key: document.root_key.0,
        }
    }

    fn with_indent(&self, config: &Config) -> Self {
        if !config.is_pretty {
            return self.clone();
        }

        State {
            is_pretty: self.is_pretty,
            indent: self.indent + config.indent,
            key: self.key,
            doc: self.doc,
        }
    }

    fn without_pretty(&self) -> Self {
        State {
            is_pretty: false,
            indent: 0,
            key: self.key,
            doc: self.doc,
        }
    }

    fn with_key(&self, key: DocKey) -> Self {
        State {
            is_pretty: self.is_pretty,
            indent: self.indent,
            key,
            doc: self.doc,
        }
    }
}

impl Print<Config, State<'_>> for Declaration {
    fn print(
        &self,
        f: &mut dyn Write,
        _config: &Config,
        context: &State<'_>,
    ) -> std::io::Result<()> {
        write!(f, "<?xml")?;

        if let Some(version) = self.version.as_deref() {
            write!(f, " version=\"{}\"", version)?;
        }

        if let Some(encoding) = self.encoding.as_deref() {
            write!(f, " encoding=\"{}\"", encoding)?;
        }

        if let Some(standalone) = self.standalone.as_deref() {
            write!(f, " standalone=\"{}\"", standalone)?;
        }

        write!(f, "?>")?;

        if context.is_pretty {
            writeln!(f)?;
        }

        Ok(())
    }
}

impl Display for Document {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut config = if f.alternate() {
            Config::default_pretty()
        } else {
            Config::default()
        };

        if let Some(width) = f.width() {
            config.is_pretty = true;
            config.indent = width;
        }

        if let Some(precision) = f.precision() {
            config.is_pretty = true;
            config.max_line_length = precision;
        }

        self.print(
            &mut FmtWriter(f),
            &config,
            &State::new(self, config.is_pretty),
        )
        .map_err(|_| std::fmt::Error)
    }
}

impl Print<Config, State<'_>> for Document {
    fn print(
        &self,
        f: &mut dyn Write,
        config: &Config,
        context: &State<'_>,
    ) -> std::io::Result<()> {
        if let Some(decl) = self.decl.as_ref() {
            Print::print(decl, f, config, context)?;
        }

        for node in self.before.iter() {
            let node_value = self.nodes.get(node.as_key()).unwrap();
            node_value.print(f, config, &context.with_key(node.as_key()))?;
        }

        let element = self
            .nodes
            .get(self.root_key.0)
            .unwrap()
            .as_element()
            .unwrap();

        element.print(f, config, &context.with_key(self.root_key.0))?;

        for node in self.after.iter() {
            let node_value = self.nodes.get(node.as_key()).unwrap();
            node_value.print(f, config, &context.with_key(node.as_key()))?;
        }

        Ok(())
    }
}

fn fmt_attrs(
    f: &mut dyn Write,
    tag: &QName,
    config: &Config,
    context: &State,
    attrs: &IndexMap<QName, String>,
) -> io::Result<()> {
    let line_length = tag.prefixed_name().len()
        + 2
        + attrs.iter().fold(0usize, |acc, (k, v)| {
            acc + k.prefixed_name().len() + v.len() + 4
        });

    let is_newlines = context.is_pretty && line_length > config.max_line_length;
    let context = context.with_indent(config);

    let mut iter = attrs.iter();

    if let Some((k, v)) = iter.next() {
        write!(
            f,
            "{}=\"{}\"",
            k,
            process_entities(v, config.entity_mode, false, false)
        )?;
    }

    if let Some((k, v)) = iter.next() {
        if is_newlines {
            writeln!(f)?;
            write!(f, "{:>indent$}", "", indent = context.indent)?;
        } else {
            write!(f, " ")?;
        }
        write!(
            f,
            "{}=\"{}\"",
            k,
            process_entities(v, config.entity_mode, false, false)
        )?;
    } else {
        return Ok(());
    }

    for (k, v) in iter {
        if is_newlines {
            writeln!(f)?;
            write!(f, "{:>indent$}", "", indent = context.indent)?;
        } else {
            write!(f, " ")?;
        }
        write!(
            f,
            "{}=\"{}\"",
            k,
            process_entities(v, config.entity_mode, false, false)
        )?;
    }

    Ok(())
}

/// Renders an element onto a single line into a scratch buffer.
///
/// By default only text-only content is inlined: a child *element* (or other node kind such as
/// a comment or processing instruction) causes this to return `None`, so those nest onto their
/// own lines. When [`Config::tight`] is set, the entire subtree is collapsed instead, recursing
/// into child elements. Either way it returns `None` if the result would contain a newline or
/// grow past `budget` bytes, signalling the caller to fall back to multi-line rendering.
/// `budget` is the line-length budget *excluding* the leading indentation.
fn try_inline(
    element: &ElementValue,
    key: DocKey,
    config: &Config,
    context: &State,
    budget: usize,
) -> Option<String> {
    let mut buf = String::new();
    flat_element(&mut buf, element, key, config, context, budget)?;
    Some(buf)
}

fn flat_element(
    buf: &mut String,
    element: &ElementValue,
    key: DocKey,
    config: &Config,
    context: &State,
    budget: usize,
) -> Option<()> {
    use std::fmt::Write as _;

    let _ = write!(buf, "<{}", element.name);
    if let Some(attrs) = context.doc.attrs.get(key) {
        for (k, v) in attrs.iter() {
            let _ = write!(
                buf,
                " {}=\"{}\"",
                k,
                process_entities(v, config.entity_mode, false, false)
            );
            check(buf, budget)?;
        }
    }

    // Only reached for empty child elements while recursing in tight mode; the top-level
    // empty case is handled earlier in `ElementValue::print`.
    if element.children.is_empty() {
        let _ = write!(buf, "{:>end_pad$}/>", "", end_pad = config.end_pad);
        return check(buf, budget);
    }

    let _ = write!(buf, ">");
    check(buf, budget)?;

    let last = element.children.len() - 1;
    for (i, child) in element.children.iter().enumerate() {
        match context.doc.nodes.get(child.as_key())? {
            NodeValue::Element(e) => {
                // Child elements nest onto their own lines unless tight mode is enabled.
                if !config.tight {
                    return None;
                }
                flat_element(buf, e, child.as_key(), config, context, budget)?;
            }
            NodeValue::Text(t) => {
                // Trim only the content boundaries: leading whitespace of the first child and
                // trailing whitespace of the last child. Whitespace *between* siblings is
                // significant and is preserved.
                let mut s: &str = t;
                if i == 0 {
                    s = s.trim_start();
                }
                if i == last {
                    s = s.trim_end();
                }
                let _ = write!(
                    buf,
                    "{}",
                    process_entities(s, config.entity_mode, true, true)
                );
            }
            NodeValue::CData(t) => {
                let _ = write!(buf, "<![CDATA[{t}]]>");
            }
            NodeValue::Comment(t) => {
                if !config.tight {
                    return None;
                }
                let _ = write!(buf, "<!--{t}-->");
            }
            NodeValue::ProcessingInstruction(t) => {
                if !config.tight {
                    return None;
                }
                let _ = write!(buf, "<?{t}?>");
            }
            // A doctype is never a legal element child; refuse to inline if we hit one.
            NodeValue::DocumentType(_) => return None,
        }
        check(buf, budget)?;
    }

    let _ = write!(buf, "</{}>", element.name);
    check(buf, budget)
}

/// Bails out (`None`) once the buffer overflows `budget` or contains a newline.
#[inline]
fn check(buf: &str, budget: usize) -> Option<()> {
    if buf.len() > budget || buf.as_bytes().contains(&b'\n') {
        None
    } else {
        Some(())
    }
}

impl Print<Config, State<'_>> for ElementValue {
    fn print(
        &self,
        f: &mut dyn Write,
        config: &Config,
        context: &State<'_>,
    ) -> std::io::Result<()> {
        if self.children.is_empty() {
            match context.doc.attrs.get(context.key) {
                Some(attrs) if !attrs.is_empty() => {
                    write!(f, "{:>indent$}<{}", "", self.name, indent = context.indent)?;
                    let line_length = &self.name.prefixed_name().len()
                        + 2
                        + attrs.iter().take(1).fold(0usize, |acc, (k, v)| {
                            acc + k.prefixed_name().len() + v.len() + 4
                        });
                    let is_newlines = context.is_pretty && line_length > config.max_line_length;
                    if is_newlines {
                        writeln!(f)?;
                        write!(
                            f,
                            "{:>indent$}",
                            "",
                            indent = context.indent + config.indent
                        )?;
                    } else {
                        write!(f, " ")?;
                    }
                    fmt_attrs(f, &self.name, config, context, attrs)?;
                    write!(f, "{:>end_pad$}/>", "", end_pad = config.end_pad)?;
                    if context.is_pretty {
                        writeln!(f)?;
                    }
                    return Ok(());
                }
                _ => {
                    write!(
                        f,
                        "{:>indent$}<{:>end_pad$}/>",
                        "",
                        self.name,
                        indent = context.indent,
                        end_pad = config.end_pad
                    )?;
                    if context.is_pretty {
                        writeln!(f)?;
                    }
                    return Ok(());
                }
            }
        }

        let has_text = self
            .children
            .iter()
            .any(|x| matches!(x, Node::Text(_) | Node::CDataSection(_)));

        // Keep text-only content on a single line when it fits within `max_line_length`.
        // Elements with child elements still nest onto their own lines (handled below).
        if context.is_pretty {
            let budget = config.max_line_length.saturating_sub(context.indent);
            if let Some(inline) = try_inline(self, context.key, config, context, budget) {
                writeln!(f, "{:>indent$}{inline}", "", indent = context.indent)?;
                return Ok(());
            }
        }

        match context.doc.attrs.get(context.key) {
            Some(attrs) if !attrs.is_empty() => {
                write!(f, "{:>indent$}<{}", "", self.name, indent = context.indent)?;
                let line_length = &self.name.prefixed_name().len()
                    + 2
                    + attrs.iter().take(1).fold(0usize, |acc, (k, v)| {
                        acc + k.prefixed_name().len() + v.len() + 4
                    });
                let is_newlines = context.is_pretty && line_length > config.max_line_length;
                if is_newlines {
                    writeln!(f)?;
                    write!(
                        f,
                        "{:>indent$}",
                        "",
                        indent = context.indent + config.indent
                    )?;
                } else {
                    write!(f, " ")?;
                }
                fmt_attrs(f, &self.name, config, context, attrs)?;
                write!(f, ">")?;
                if (config.indent_text_nodes || !has_text) && context.is_pretty {
                    writeln!(f)?;
                }
            }
            _ => {
                write!(f, "{:>indent$}<{}>", "", self.name, indent = context.indent)?;
                if (config.indent_text_nodes || !has_text) && context.is_pretty {
                    writeln!(f)?;
                }
            }
        }

        let child_context = {
            if has_text && !config.indent_text_nodes {
                context.without_pretty()
            } else {
                context.with_indent(config)
            }
        };

        for child in self.children.iter() {
            let value = context.doc.nodes.get(child.as_key()).unwrap();
            value.print(f, config, &child_context.with_key(child.as_key()))?;
        }

        if (config.indent_text_nodes || !has_text) && context.is_pretty {
            write!(
                f,
                "{:>indent$}</{}>",
                "",
                self.name,
                indent = context.indent
            )?;

            writeln!(f)?;
        } else {
            write!(f, "</{}>", self.name)?;
            if context.is_pretty {
                writeln!(f)?;
            }
        }

        Ok(())
    }
}

impl Print<Config, State<'_>> for NodeValue {
    fn print(
        &self,
        f: &mut dyn Write,
        config: &Config,
        context: &State<'_>,
    ) -> std::io::Result<()> {
        if let NodeValue::Element(e) = self {
            return e.print(f, config, context);
        }

        if let NodeValue::Text(t) = self {
            if config.indent_text_nodes && context.is_pretty {
                writeln!(
                    f,
                    "{:>indent$}{content}",
                    "",
                    indent = context.indent,
                    // If `indent_text_nodes`+`is_pretty` is set, surrounding whitespace can be
                    // assumed to be non-significant. In order to avoid producing ever-increasing
                    // surrounding space in read-write loops, trim the existing whitespace to
                    // replace it with our own.
                    content = &*process_entities(t.trim(), config.entity_mode, true, true)
                )?;
            } else {
                write!(
                    f,
                    "{}",
                    &*process_entities(t, config.entity_mode, true, true)
                )?;
            }

            return Ok(());
        }

        if let NodeValue::CData(t) = self {
            if config.indent_text_nodes && context.is_pretty {
                write!(f, "{:>indent$}", "", indent = context.indent)?;
            }

            write!(f, "<![CDATA[{t}]]>")?;

            if config.indent_text_nodes && context.is_pretty {
                writeln!(f)?;
            }

            return Ok(());
        }

        if context.is_pretty {
            write!(f, "{:>indent$}", "", indent = context.indent)?;
        }

        match self {
            NodeValue::DocumentType(t) => write!(f, "<!DOCTYPE {}>", t),
            NodeValue::Comment(t) => write!(f, "<!--{}-->", t),
            NodeValue::ProcessingInstruction(t) => write!(f, "<?{}?>", t),
            NodeValue::Element(_) | NodeValue::Text(_) | NodeValue::CData(_) => unreachable!(),
        }?;

        if context.is_pretty {
            writeln!(f)?;
        }

        Ok(())
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum EntityMode {
    #[default]
    Standard,
    Hex,
}

fn process_entities(
    input: &str,
    mode: EntityMode,
    allow_separators: bool,
    is_text: bool,
) -> Cow<'_, str> {
    if input.chars().any(|ch| {
        if ['<', '>', '\'', '"', '&'].contains(&ch) || ch.is_ascii_control() {
            return true;
        }
        let cat = GeneralCategory::of(ch);
        cat.is_separator() || cat.is_other()
    }) {
        let mut s = String::with_capacity(input.len());
        input.chars().for_each(|ch| {
            s.push_str(match (mode, ch) {
                (EntityMode::Standard, '&') => "&amp;",
                (EntityMode::Standard, '\'') if !is_text => "&apos;",
                (EntityMode::Standard, '"') if !is_text => "&quot;",
                (EntityMode::Standard, '<') => "&lt;",
                (EntityMode::Standard, '>') => "&gt;",
                (EntityMode::Hex, '&' | '\'' | '"' | '<' | '>') => {
                    s.push_str(&format!("&#x{:>04X};", ch as u32));
                    return;
                }
                (_, ch) if !ch.is_ascii_whitespace() && ch.is_ascii_control() => {
                    s.push_str(&format!("&#x{:>04X};", ch as u32));
                    return;
                }
                (_, other) => {
                    let cat = GeneralCategory::of(other);

                    let is_ws = ch != '\u{00a0}'
                        && (ch == ' '
                            || allow_separators
                                && (other.is_ascii_whitespace() || cat.is_separator()));
                    let is_printable = !(cat.is_separator() || cat.is_other());

                    if is_ws || is_printable {
                        s.push(other);
                    } else {
                        s.push_str(&format!("&#x{:>04X};", ch as u32));
                    }
                    return;
                }
            })
        });
        Cow::Owned(s)
    } else {
        Cow::Borrowed(input)
    }
}

struct FmtWriter<'a, 'b>(&'b mut std::fmt::Formatter<'a>);

impl Write for FmtWriter<'_, '_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let s = std::str::from_utf8(buf).map_err(io::Error::other)?;
        self.0.write_str(s).map_err(io::Error::other)?;
        Ok(s.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
