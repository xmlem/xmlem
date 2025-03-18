use std::{
    cmp::{min, Ordering},
    error::Error,
    fmt,
    io::BufRead,
    str::Utf8Error,
};

use indexmap::IndexMap;
use once_cell::sync::Lazy;
use qname::QName;
use slotmap::{SlotMap, SparseSecondaryMap};

use crate::{
    display::{self, Config, Print, State},
    element::Element,
    key::{CDataSection, Comment, DocKey, DocumentType, Text},
    value::{ElementValue, NodeValue},
    NewElement, Node,
};
use tracing::debug;

static ATTR_ID: Lazy<QName> = Lazy::new(|| QName::new("id").unwrap());

#[derive(Debug, Clone)]
pub struct Document {
    pub(crate) nodes: SlotMap<DocKey, NodeValue>,
    pub(crate) parents: SparseSecondaryMap<DocKey, Element>,
    pub(crate) attrs: SparseSecondaryMap<DocKey, IndexMap<QName, String>>,
    pub(crate) root_key: Element,
    pub(crate) before: Vec<Node>,
    pub(crate) after: Vec<Node>,
    pub(crate) decl: Option<Declaration>,
}

#[derive(Debug, Clone)]
pub struct Declaration {
    pub version: Option<String>,
    pub encoding: Option<String>,
    pub standalone: Option<String>,
}

impl Declaration {
    pub fn v1_0() -> Self {
        Self {
            version: Some("1.0".to_string()),
            encoding: Some("utf-8".to_string()),
            standalone: None,
        }
    }

    pub fn v1_1() -> Self {
        Self {
            version: Some("1.1".to_string()),
            encoding: Some("utf-8".to_string()),
            standalone: None,
        }
    }
}

pub struct ElementAndContext<'a> {
    pre: Vec<&'a Node>,
    elem: &'a Node,
    attrs: &'a IndexMap<QName, String>,
    elem_val: &'a ElementValue,
}

pub fn ord_node(n1: &&Node, n2: &&Node) -> Ordering {
    n1.to_ordinal().cmp(&n2.to_ordinal())
}

pub fn ord_elem(ec1: &ElementAndContext, ec2: &ElementAndContext) -> Ordering {
    let e1 = ec1.elem_val;
    let e2 = ec2.elem_val;

    // 1. Order by element name
    let name_ord = e1.name.cmp(&e2.name);
    if !matches!(name_ord, Ordering::Equal) {
        return name_ord;
    }

    // 2. Order by the 'id' attributes value, if both elements contain it
    if let Some(e1_id) = ec1.attrs.get::<QName>(&ATTR_ID) {
        if let Some(e2_id) = ec2.attrs.get::<QName>(&ATTR_ID) {
            let id_ord = e1_id.cmp(e2_id);
            if !matches!(id_ord, Ordering::Equal) {
                return id_ord;
            }
        }
    }

    // 3. Order by name of all the attributes of the two elements
    // NOTE We assume/require attributes to already be sorted by name!
    let mut e1_attrs_names = ec1.attrs.keys();
    let mut e2_attrs_names = ec2.attrs.keys();
    let min_len = min(ec1.attrs.len(), ec2.attrs.len());
    for _ai in 0..min_len {
        let e1_ak = e1_attrs_names.next();
        let e2_ak = e2_attrs_names.next();
        let attrs_ord = e1_ak.cmp(&e2_ak);
        if !matches!(attrs_ord, Ordering::Equal) {
            return attrs_ord;
        }
    }

    // 4. Order by number of attributes
    let num_attrs_ord = ec1.attrs.len().cmp(&ec2.attrs.len());
    if num_attrs_ord.is_ne() {
        return num_attrs_ord;
    }

    // 5. Order by values of attributes
    let mut e1_attrs_values = ec1.attrs.values();
    let mut e2_attrs_values = ec2.attrs.values();
    for _ai in 0..min_len {
        let e1_av = e1_attrs_values.next();
        let e2_av = e2_attrs_values.next();
        let attrs_ord = e1_av.cmp(&e2_av);
        if !matches!(attrs_ord, Ordering::Equal) {
            return attrs_ord;
        }
    }

    Ordering::Equal
}

impl Document {
    /// Create a new document with the specified element as root.
    ///
    /// See [`NewElement`] for what `root` accepts.
    ///
    /// ```
    /// assert_eq!(
    ///     xmlem::Document::new("root").to_string(),
    ///     r#"<root/>"#,
    /// );
    /// assert_eq!(
    ///     xmlem::Document::new(("a", [("b", "c")])).to_string(),
    ///     r#"<a b="c"/>"#,
    /// );
    /// ```
    ///
    /// # Panics
    ///
    /// This method panics if `root` contains non-representable element or attribute names.
    pub fn new(root: impl Into<NewElement>) -> Self {
        let root = root.into();

        let mut nodes = SlotMap::with_key();
        let parents = SparseSecondaryMap::new();
        let mut attrs = SparseSecondaryMap::<DocKey, IndexMap<QName, String>>::new();

        let root_key = Element(nodes.insert(NodeValue::Element(ElementValue {
            name: root.name,
            children: vec![],
        })));
        attrs.insert(root_key.0, root.attrs);

        Self {
            nodes,
            parents,
            attrs,
            root_key,
            before: vec![],
            after: vec![],
            decl: None,
        }
    }

    fn sort_nodes(&self, nodes_orig: &[Node]) -> Vec<Node> {
        if nodes_orig.len() < 2 {
            return nodes_orig.to_owned();
        }

        let nodes = nodes_orig.to_owned();

        let mut pre = vec![];
        let mut elems = vec![];
        let mut has_text = false;
        let mut post = vec![];
        for node in &nodes {
            match node {
                Node::Element(elem) => {
                    elems.push(ElementAndContext {
                        pre: pre.clone(),
                        elem: node,
                        attrs: self.attrs.get(elem.0).unwrap(),
                        elem_val: self.nodes.get(elem.0).unwrap().as_element().unwrap(),
                    });
                }
                Node::Text(_) => {
                    has_text = true;
                    post.push(node);
                }
                Node::CDataSection(_) => pre.push(node),
                Node::ProcessingInstruction(_) => post.push(node),
                Node::Comment(_) => pre.push(node),
                Node::DocumentType(_) => {
                    panic!("DocumentType found inside an element; that should never be the case")
                }
            }
        }
        if has_text && !elems.is_empty() {
            debug!(
                "Element contains both element(s) and text; \
            we thus consider all elements to be inline-elements \
            (think of the *bold* element in HTML), and thus we will not sort them."
            );
            return nodes_orig.to_owned();
        }

        elems.sort_by(ord_elem);
        post.sort_by(ord_node);

        let mut nodes_sorted = vec![];
        for mut elem_cont in elems {
            elem_cont.pre.sort_by(ord_node);
            for p in elem_cont.pre {
                nodes_sorted.push(*p);
            }
            nodes_sorted.push(*elem_cont.elem);
        }
        for p in post {
            nodes_sorted.push(*p);
        }
        nodes_sorted
    }

    fn sort_node_value(&self, node_value: &NodeValue) -> NodeValue {
        let mut new_node_value = node_value.clone();
        if let NodeValue::Element(ref mut e) = new_node_value {
            e.children = self.sort_nodes(&e.children);
        }
        new_node_value
    }

    fn sort_attrs(&mut self) {
        for el_attrs in self.attrs.values_mut() {
            el_attrs.sort_by(|qn1: &QName, _v1: &String, qn2: &QName, _v2: &String| qn1.cmp(qn2));
        }
    }

    pub fn sort(&mut self, elements: bool) {
        self.sort_attrs();
        if elements {
            self.before = self.sort_nodes(&self.before);
            self.nodes[self.root_key.0] = self.sort_node_value(&self.nodes[self.root_key.0]);
            self.after = self.sort_nodes(&self.after);
        }
    }

    pub fn set_declaration(&mut self, decl: Option<Declaration>) {
        self.decl = decl;
    }

    pub fn declaration(&self) -> Option<&Declaration> {
        self.decl.as_ref()
    }

    pub fn set_doctype(&mut self, doctype: Option<&str>) {
        match doctype {
            Some(v) => {
                let id = Node::DocumentType(DocumentType(
                    self.nodes.insert(NodeValue::DocumentType(v.to_string())),
                ));

                for i in 0..self.before.len() {
                    if self.before[i].as_document_type().is_some() {
                        self.nodes.remove(self.before[i].as_key());
                        self.before[i] = id;
                        return;
                    }
                }

                // If that failed, push it ourselves.
                self.before.insert(0, id);
            }
            None => {
                for i in 0..self.before.len() {
                    if self.before[i].as_document_type().is_some() {
                        self.before.remove(i);
                        return;
                    }
                }
            }
        }
    }

    pub fn doctype(&self) -> Option<&str> {
        for i in 0..self.before.len() {
            if let Some(v) = self.before[i].as_document_type() {
                return Some(self.nodes.get(v.0).unwrap().as_document_type().unwrap());
            }
        }

        None
    }

    #[inline]
    pub fn root(&self) -> Element {
        self.root_key
    }

    #[inline]
    pub fn to_string_pretty(&self) -> String {
        let mut s = vec![];
        self.print(&mut s, &Config::default_pretty(), &State::new(self, true))
            .unwrap();
        String::from_utf8(s).expect("invalid UTF-8")
    }

    #[inline]
    pub fn to_string_pretty_with_config(&self, config: &display::Config) -> String {
        let mut s = vec![];
        self.print(&mut s, config, &State::new(self, true)).unwrap();
        String::from_utf8(s).expect("invalid UTF-8")
    }

    #[inline]
    pub fn from_file(file: std::fs::File) -> Result<Document, ReadError> {
        let reader = std::io::BufReader::new(file);
        Self::from_reader(reader)
    }

    #[inline]
    pub fn from_reader<R: BufRead>(reader: R) -> Result<Document, ReadError> {
        use quick_xml::events::Event;
        use quick_xml::Reader;

        let mut r = Reader::from_reader(reader);
        let mut buf = Vec::new();

        let mut decl: Option<Declaration> = None;

        let mut nodes = SlotMap::with_key();
        let parents = SparseSecondaryMap::new();
        let attrs = SparseSecondaryMap::new();

        let mut before: Vec<Node> = vec![];
        let mut element_stack = vec![];

        let mut doc = loop {
            match r.read_event_into(&mut buf) {
                Ok(Event::DocType(d)) => {
                    before.push(Node::DocumentType(DocumentType(
                        nodes.insert(NodeValue::DocumentType(d.unescape()?.trim().to_string())),
                    )));
                }
                Ok(Event::Decl(d)) => {
                    let version = d
                        .version()
                        .ok()
                        .and_then(|x| std::str::from_utf8(&x).ok().map(ToString::to_string));
                    let standalone = d.standalone().and_then(|x| match x {
                        Ok(x) => std::str::from_utf8(&x).ok().map(ToString::to_string),
                        Err(_) => None,
                    });
                    let encoding = d.encoding().and_then(|x| match x {
                        Ok(x) => std::str::from_utf8(&x).ok().map(ToString::to_string),
                        Err(_) => None,
                    });

                    decl = Some(Declaration {
                        version,
                        standalone,
                        encoding,
                    });
                }
                Ok(ref x @ (Event::Start(ref e) | Event::Empty(ref e))) => {
                    let name: QName = std::str::from_utf8(e.name().into_inner())?.parse()?;

                    let root_key = Element(nodes.insert(NodeValue::Element(ElementValue {
                        name,
                        children: vec![],
                    })));

                    let mut document = Document {
                        nodes,
                        parents,
                        attrs,
                        root_key,
                        decl,
                        before,
                        after: vec![],
                    };

                    let root = document.root();

                    if matches!(x, Event::Start(_)) {
                        element_stack.push(root);
                    }

                    for attr in e.attributes().filter_map(Result::ok) {
                        let value = attr.decode_and_unescape_value(r.decoder())?;
                        let s = std::str::from_utf8(attr.key.into_inner())?;

                        root.set_attribute(&mut document, s.parse::<QName>()?, &value);
                    }

                    break document;
                }
                Ok(Event::Text(e)) => {
                    if e.len() == 0 {
                        continue;
                    }
                    if e.unescape().map(|x| x.trim().is_empty()).unwrap_or(false) {
                        continue;
                    }
                    before.push(Node::Text(Text(
                        nodes.insert(NodeValue::Text(e.unescape()?.to_string())),
                    )));
                }
                Ok(Event::Comment(e)) => {
                    before.push(Node::Comment(Comment(
                        nodes.insert(NodeValue::Comment(e.unescape()?.to_string())),
                    )));
                }
                Ok(Event::CData(e)) => {
                    let e_inner = e.into_inner();
                    let text = std::str::from_utf8(e_inner.as_ref())?;
                    before.push(Node::CDataSection(CDataSection(
                        nodes.insert(NodeValue::CData(text.to_owned())),
                    )));
                }
                Ok(Event::PI(_)) => {
                    continue;
                }
                Ok(other @ (Event::Eof | Event::End(_))) => {
                    return Err(ReadError::Unexpected(format!("{other:?}")))
                }
                Err(e) => return Err(e.into()),
            }
        };

        loop {
            match r.read_event_into(&mut buf) {
                Ok(Event::Start(e)) => {
                    let name: QName = std::str::from_utf8(e.name().into_inner())?.parse()?;
                    let parent = match element_stack.last() {
                        Some(v) => v,
                        None => {
                            return Err(ReadError::SupplementaryElement(
                                name.prefixed_name().to_string(),
                            ));
                        }
                    };
                    let mut attrs = IndexMap::new();
                    for attr in e.attributes().filter_map(Result::ok) {
                        let value = attr.decode_and_unescape_value(r.decoder())?.to_string();
                        attrs.insert(std::str::from_utf8(attr.key.into_inner())?.parse()?, value);
                    }
                    let element =
                        parent.append_new_element(&mut doc, crate::NewElement { name, attrs });
                    element_stack.push(element);
                }
                Ok(Event::Empty(e)) => {
                    let name: QName = std::str::from_utf8(e.name().into_inner())?.parse()?;
                    let parent = match element_stack.last() {
                        Some(v) => v,
                        None => {
                            return Err(ReadError::SupplementaryElement(
                                name.prefixed_name().to_string(),
                            ));
                        }
                    };
                    let mut attrs = IndexMap::new();
                    for attr in e.attributes().filter_map(Result::ok) {
                        let value = attr.decode_and_unescape_value(r.decoder())?.to_string();
                        attrs.insert(std::str::from_utf8(attr.key.into_inner())?.parse()?, value);
                    }
                    parent.append_new_element(&mut doc, crate::NewElement { name, attrs });
                }
                Ok(Event::End(_e)) => {
                    element_stack.pop();
                }
                Ok(Event::Text(e)) => {
                    let text = e.unescape()?;
                    if !text.trim().is_empty() {
                        match element_stack.last() {
                            Some(el) => {
                                el.append_text(&mut doc, &text);
                            }
                            None => {
                                doc.after.push(Node::Text(Text(
                                    doc.nodes.insert(NodeValue::Text(text.to_string())),
                                )));
                            }
                        }
                    }
                }
                Ok(Event::CData(cdata)) => {
                    let cdata_inner = cdata.into_inner();
                    let text = std::str::from_utf8(cdata_inner.as_ref())?;
                    match element_stack.last() {
                        Some(el) => {
                            el.append_cdata(&mut doc, text);
                        }
                        None => {
                            doc.after.push(Node::CDataSection(CDataSection(
                                doc.nodes.insert(NodeValue::CData(text.to_owned())),
                            )));
                        }
                    }
                }
                Ok(Event::Comment(comment)) => {
                    let comment = comment.into_inner();
                    let text = std::str::from_utf8(comment.as_ref())?;
                    match element_stack.last() {
                        Some(el) => {
                            el.append_comment(&mut doc, &text);
                        }
                        None => {
                            doc.after.push(Node::Comment(Comment(
                                doc.nodes.insert(NodeValue::Comment(text.to_string())),
                            )));
                        }
                    }
                }
                Ok(Event::PI(_processing_instruction)) => {
                    continue;
                }
                Ok(Event::Decl(_decl)) => {
                    continue;
                }
                Ok(Event::DocType(_doctype)) => {
                    continue;
                }
                Ok(Event::Eof) => {
                    // exits the loop when reaching end of file
                    break;
                }
                Err(e) => {
                    return Err(e.into());
                }
            }
        }

        Ok(doc)
    }
}

impl std::str::FromStr for Document {
    type Err = ReadError;

    fn from_str(s: &str) -> Result<Document, ReadError> {
        Self::from_reader(std::io::Cursor::new(s))
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum ReadError {
    Parse(quick_xml::Error),
    Encoding(Utf8Error),
    SupplementaryElement(String),
    Unexpected(String),
    Name(qname::Error),
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ReadError::Parse(err) => fmt::Display::fmt(err, f),
            ReadError::Encoding(err) => fmt::Display::fmt(err, f),
            ReadError::Name(err) => fmt::Display::fmt(err, f),
            ReadError::SupplementaryElement(name) => {
                write!(f, "Supplementary element after root: {name}")
            }
            ReadError::Unexpected(description) => {
                write!(f, "Unexpected: {description}")
            }
        }
    }
}

impl Error for ReadError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Parse(err) => err.source(),
            Self::Encoding(err) => err.source(),
            Self::Name(err) => err.source(),
            Self::SupplementaryElement(..) | Self::Unexpected(..) => None,
        }
    }
}

impl From<quick_xml::Error> for ReadError {
    fn from(err: quick_xml::Error) -> Self {
        Self::Parse(err)
    }
}

impl From<Utf8Error> for ReadError {
    fn from(err: Utf8Error) -> Self {
        Self::Encoding(err)
    }
}

impl From<qname::Error> for ReadError {
    fn from(err: qname::Error) -> Self {
        Self::Name(err)
    }
}
