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
            NodeValue::Comment(t) => write!(
                f,
                "<!--{}-->",
                process_entities(t, config.entity_mode, true, true)
            ),
            NodeValue::Element(_) | NodeValue::Text(_) | NodeValue::CData(_) => unreachable!(),
        }?;

        if context.is_pretty {
            writeln!(f)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum EntityMode {
    Standard,
    Hex,
}

impl Default for EntityMode {
    fn default() -> Self {
        Self::Standard
    }
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
        let s = std::str::from_utf8(buf).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        self.0
            .write_str(s)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        Ok(s.as_bytes().len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
