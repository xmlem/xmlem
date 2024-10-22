use indexmap::IndexMap;
use once_cell::sync::Lazy;
use qname::QName;

use crate::{
    display::{self, Print},
    document::Document,
    key::{CDataSection, Comment, DocKey, Node, Text},
    select::Selector,
    value::{ElementValue, NodeValue},
};

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct Element(pub(crate) DocKey);

impl From<Element> for Node {
    fn from(n: Element) -> Self {
        Node::Element(n)
    }
}

/// This data structure is used as a way to create new elements when using methods such as
/// [`Element::append_new_element`] or [`Element::append_element`].
///
/// For static insertions, the easiest way to define a `NewElement` is to use the [`From`]
/// trait:
///
/// ```
/// # use qname::qname;
/// let new_element: xmlem::NewElement = ("sub", [
///     ("id", "main-content"),
///     ("xml:lang", "ff")
/// ]).into();
///
/// assert_eq!(new_element.name, qname!("sub"));
/// assert_eq!(new_element.attrs.iter().collect::<Vec<_>>(), [
///     (&qname!("id"), &"main-content".to_owned()),
///     (&qname!("xml:lang"), &"ff".to_owned())
/// ]);
/// ```
///
/// Methods using `NewElement` accept this kind of tuple directly:
///
/// ```
/// let mut doc = r#"<root/>"#.parse::<xmlem::Document>().unwrap();
///
/// doc.root().append_new_element(&mut doc, ("sub", [("xml:lang", "fa")]));
///
/// assert_eq!(doc.to_string(), r#"<root><sub xml:lang="fa"/></root>"#);
/// ```
///
/// # Panics
///
/// Converting to `NewElement` panics on non-representable elements and attributes names.
#[derive(Debug, Clone)]
pub struct NewElement {
    pub name: QName,
    pub attrs: IndexMap<QName, String>,
}

impl<const N: usize, T: ToString, U: ToString, V: ToString> From<(T, [(U, V); N])> for NewElement {
    fn from(x: (T, [(U, V); N])) -> Self {
        NewElement {
            name: x.0.to_string().parse().unwrap(),
            attrs: x
                .1
                .into_iter()
                .map(|x| (x.0.to_string().parse().unwrap(), x.1.to_string()))
                .collect(),
        }
    }
}

impl Element {
    pub fn as_node(&self) -> Node {
        Node::from(*self)
    }

    /// Move an existing element to the end of the list of child nodes of the current element.
    ///
    /// ```
    /// let mut doc = r#"<root><a><c/></a><b/></root>"#.parse::<xmlem::Document>().unwrap();
    /// let a = doc.root().children(&doc)[0];
    /// let b = doc.root().children(&doc)[1];
    ///
    /// a.append_element(&mut doc, b);
    ///
    /// assert_eq!(doc.to_string(), r#"<root><a><c/><b/></a></root>"#);
    /// ```
    pub fn append_element(self, document: &mut Document, element: Element) {
        if let Some(parent) = element.parent(document) {
            parent.remove_child(document, Node::Element(element));
        }

        document.parents.insert(element.0, self);
        document
            .nodes
            .get_mut(self.0)
            .unwrap()
            .as_element_mut()
            .unwrap()
            .children
            .push(Node::Element(element));
    }

    /// Create a new element and add it to the end of the list of child nodes of the current
    /// element.
    ///
    /// See [`NewElement`] for what `new_element` accepts.
    ///
    /// ```
    /// let mut doc = r#"<root><a><b/></a></root>"#.parse::<xmlem::Document>().unwrap();
    /// let a = doc.root().children(&doc)[0];
    ///
    /// a.append_new_element(&mut doc, ("c", [("d", "e")]));
    ///
    /// assert_eq!(doc.to_string(), r#"<root><a><b/><c d="e"/></a></root>"#);
    /// ```
    ///
    /// # Panics
    ///
    /// This method panics if `new_element` contains non-representable element or attribute names.
    pub fn append_new_element(
        self,
        document: &mut Document,
        new_element: impl Into<NewElement>,
    ) -> Element {
        let element = new_element.into();
        let new_key = document.nodes.insert(NodeValue::Element(ElementValue {
            name: element.name,
            children: vec![],
        }));
        document.attrs.insert(new_key, element.attrs);
        document.parents.insert(new_key, self);
        document
            .nodes
            .get_mut(self.0)
            .unwrap()
            .as_element_mut()
            .unwrap()
            .children
            .push(Node::Element(Element(new_key)));
        Element(new_key)
    }

    /// Create a new element and add it to the list of child nodes of the parent of the current
    /// element, right after the current element.
    ///
    /// See [`NewElement`] for what `new_element` accepts.
    ///
    /// ```
    /// let mut doc = r#"<root><a><b/></a></root>"#.parse::<xmlem::Document>().unwrap();
    /// let a = doc.root().children(&doc)[0];
    ///
    /// a.append_new_element_after(&mut doc, ("c", [("d", "e")]));
    ///
    /// assert_eq!(doc.to_string(), r#"<root><a><b/></a><c d="e"/></root>"#);
    /// ```
    ///
    /// # Panics
    ///
    /// This method panics if `new_element` contains non-representable element or attribute names.
    pub fn append_new_element_after(
        self,
        document: &mut Document,
        new_element: impl Into<NewElement>,
    ) -> Element {
        let element = new_element.into();
        let new_key = document.nodes.insert(NodeValue::Element(ElementValue {
            name: element.name,
            children: vec![],
        }));
        document.attrs.insert(new_key, element.attrs);

        let parent = self.parent(document).expect("no parent");
        document.parents.insert(new_key, parent);

        let children = &mut document
            .nodes
            .get_mut(parent.0)
            .unwrap()
            .as_element_mut()
            .unwrap()
            .children;

        let index = children.iter().position(|x| x == &self.as_node()).unwrap() + 1;
        if index >= children.len() {
            children.push(Node::Element(Element(new_key)));
        } else {
            children.insert(index, Node::Element(Element(new_key)))
        }

        Element(new_key)
    }

    /// Create a new text node and add it to the end of the list of child nodes of the current
    /// element.
    ///
    /// ```
    /// let mut doc = r#"<root><a/></root>"#.parse::<xmlem::Document>().unwrap();
    ///
    /// doc.root().append_text(&mut doc, "Foo");
    ///
    /// assert_eq!(doc.to_string(), r#"<root><a/>Foo</root>"#);
    /// ```
    pub fn append_text(self, document: &mut Document, text: &str) -> Text {
        let new_key = document.nodes.insert(NodeValue::Text(text.to_string()));
        document.parents.insert(new_key, self);
        document
            .nodes
            .get_mut(self.0)
            .unwrap()
            .as_element_mut()
            .unwrap()
            .children
            .push(Node::Text(Text(new_key)));
        Text(new_key)
    }

    /// Create a new CDATA node and add it to the end of the list of child nodes of the current
    /// element.
    ///
    /// ```
    /// let mut doc = r#"<root><a/></root>"#.parse::<xmlem::Document>().unwrap();
    ///
    /// doc.root().append_cdata(&mut doc, "Foo");
    ///
    /// assert_eq!(doc.to_string(), r#"<root><a/><![CDATA[Foo]]></root>"#);
    /// ```
    pub fn append_cdata(self, document: &mut Document, text: &str) -> CDataSection {
        let new_key = document.nodes.insert(NodeValue::CData(text.to_string()));
        document.parents.insert(new_key, self);
        document
            .nodes
            .get_mut(self.0)
            .unwrap()
            .as_element_mut()
            .unwrap()
            .children
            .push(Node::CDataSection(CDataSection(new_key)));
        CDataSection(new_key)
    }

    /// Create a new comment node and add it to the end of the list of child nodes of the current
    /// element.
    ///
    /// ```
    /// let mut doc = r#"<root><a/></root>"#.parse::<xmlem::Document>().unwrap();
    ///
    /// doc.root().append_comment(&mut doc, "Foo");
    ///
    /// assert_eq!(doc.to_string(), r#"<root><a/><!--Foo--></root>"#);
    /// ```
    pub fn append_comment(self, document: &mut Document, text: &str) -> Comment {
        let new_key = document.nodes.insert(NodeValue::Comment(text.to_string()));
        document.parents.insert(new_key, self);
        document
            .nodes
            .get_mut(self.0)
            .unwrap()
            .as_element_mut()
            .unwrap()
            .children
            .push(Node::Comment(Comment(new_key)));
        Comment(new_key)
    }

    /// Replace all children nodes of the current element with a text node.
    ///
    /// ```
    /// let mut doc = r#"<root><a/></root>"#.parse::<xmlem::Document>().unwrap();
    ///
    /// doc.root().set_text(&mut doc, "Foo");
    ///
    /// assert_eq!(doc.to_string(), r#"<root>Foo</root>"#);
    /// ```
    pub fn set_text(self, document: &mut Document, text: &str) {
        let new_key = document.nodes.insert(NodeValue::Text(text.to_string()));
        document
            .nodes
            .get_mut(self.0)
            .unwrap()
            .as_element_mut()
            .unwrap()
            .children = vec![Node::Text(Text(new_key))];
    }

    /// Remove a node from the children of the current element.
    ///
    /// ```
    /// let mut doc = r#"<root>Foo<a/></root>"#.parse::<xmlem::Document>().unwrap();
    /// let a = doc.root().children(&doc)[0];
    ///
    /// doc.root().remove_child(&mut doc, a.as_node());
    ///
    /// assert_eq!(doc.to_string(), r#"<root>Foo</root>"#);
    /// ```
    ///
    /// If the given node is not a child of the current element, this method is a no-op:
    ///
    /// ```
    /// let mut doc = r#"<root><a/><b/></root>"#.parse::<xmlem::Document>().unwrap();
    /// let a = doc.root().children(&doc)[0];
    /// let b = doc.root().children(&doc)[1];
    ///
    /// a.remove_child(&mut doc, b.as_node());
    ///
    /// assert_eq!(doc.to_string(), r#"<root><a/><b/></root>"#);
    /// ```
    pub fn remove_child(self, document: &mut Document, node: Node) {
        let element = document
            .nodes
            .get_mut(self.0)
            .unwrap()
            .as_element_mut()
            .unwrap();
        match element.children.iter().position(|x| x == &node) {
            Some(i) => {
                element.children.remove(i);
            }
            None => return,
        }
        document.parents.remove(node.as_key());
    }

    /// Get the parent of the current element, if any.
    ///
    /// ```
    /// let doc = r#"<root>Foo<a/></root>"#.parse::<xmlem::Document>().unwrap();
    /// let a = doc.root().children(&doc)[0];
    ///
    /// assert_eq!(doc.root().parent(&doc), None);
    /// assert_eq!(a.parent(&doc), Some(doc.root()));
    /// ```
    pub fn parent(self, document: &Document) -> Option<Element> {
        document.parents.get(self.0).copied()
    }

    /// Get all child nodes of the current element.
    ///
    /// ```
    /// let doc = r#"<root>Foo<a/></root>"#.parse::<xmlem::Document>().unwrap();
    ///
    /// assert_eq!(doc.root().child_nodes(&doc).len(), 2);
    /// assert!(matches!(
    ///     doc.root().child_nodes(&doc)[0],
    ///     xmlem::key::Node::Text(t) if t.as_str(&doc) == "Foo"
    /// ));
    /// assert!(matches!(
    ///     doc.root().child_nodes(&doc)[1],
    ///     xmlem::key::Node::Element(e) if e.name(&doc) == "a"
    /// ));
    /// ```
    pub fn child_nodes(self, document: &Document) -> &[Node] {
        let element = document.nodes.get(self.0).unwrap().as_element().unwrap();
        &element.children
    }

    /// Get all child elements of the current element.
    ///
    /// ```
    /// let doc = r#"<root>Foo<a/></root>"#.parse::<xmlem::Document>().unwrap();
    ///
    /// assert_eq!(doc.root().children(&doc).len(), 1);
    /// assert_eq!(doc.root().children(&doc)[0].name(&doc), "a");
    /// ```
    pub fn children(self, document: &Document) -> Vec<Element> {
        let element = document.nodes.get(self.0).unwrap().as_element().unwrap();
        element
            .children
            .iter()
            .filter_map(|x| x.as_element())
            .collect()
    }

    /// Get the qualified name of this element, already parsed.
    ///
    /// ```
    /// let doc = r#"<root/>"#.parse::<xmlem::Document>().unwrap();
    /// assert_eq!(doc.root().qname(&doc).namespace(), None);
    /// assert_eq!(doc.root().qname(&doc).local_part(), "root");
    /// ```
    ///
    /// ```
    /// let doc = r#"<x:root xmlns:x="http://example.com"/>"#.parse::<xmlem::Document>().unwrap();
    /// assert_eq!(doc.root().qname(&doc).namespace(), Some("x"));
    /// assert_eq!(doc.root().qname(&doc).local_part(), "root");
    /// ```
    pub fn qname<'d>(&self, document: &'d Document) -> &'d QName {
        let element = document.nodes.get(self.0).unwrap().as_element().unwrap();
        &element.name
    }

    /// Get the unparsed qualified name of this element.
    ///
    /// ```
    /// let doc = r#"<root/>"#.parse::<xmlem::Document>().unwrap();
    /// assert_eq!(doc.root().name(&doc), "root");
    /// ```
    ///
    /// ```
    /// let doc = r#"<x:root xmlns:x="http://example.com"/>"#.parse::<xmlem::Document>().unwrap();
    /// assert_eq!(doc.root().name(&doc), "x:root");
    /// ```
    pub fn name<'d>(&self, document: &'d Document) -> &'d str {
        self.qname(document).prefixed_name()
    }

    /// Get the prefix of this element’s name.
    ///
    /// ```
    /// let doc = r#"<root/>"#.parse::<xmlem::Document>().unwrap();
    /// assert_eq!(doc.root().prefix(&doc), None);
    /// ```
    ///
    /// ```
    /// let doc = r#"<x:root xmlns:x="http://example.com"/>"#.parse::<xmlem::Document>().unwrap();
    /// assert_eq!(doc.root().prefix(&doc), Some("x"));
    /// ```
    pub fn prefix<'d>(&self, document: &'d Document) -> Option<&'d str> {
        self.qname(document).namespace()
    }

    /// List of attributes on this element, in order.
    ///
    /// ```
    /// # use qname::qname;
    /// let doc = r#"<root a:b="c" d="e"/>"#.parse::<xmlem::Document>().unwrap();
    /// let mut attrs = doc.root().attributes(&doc).iter();
    /// assert_eq!(attrs.next(), Some((&qname!("a:b"), &"c".to_owned())));
    /// assert_eq!(attrs.next(), Some((&qname!("d"), &"e".to_owned())));
    /// assert_eq!(attrs.next(), None);
    /// ```
    pub fn attributes<'d>(&self, document: &'d Document) -> &'d IndexMap<QName, String> {
        match document.attrs.get(self.0) {
            Some(x) => x,
            None => &EMPTY_INDEXMAP,
        }
    }

    /// Get the value of an attribute on this element, if present.
    ///
    /// ```
    /// # use qname::qname;
    /// let doc = r#"<root a:b="c" d="e"/>"#.parse::<xmlem::Document>().unwrap();
    /// assert_eq!(doc.root().attribute(&doc, "a:b"), Some("c"));
    /// assert_eq!(doc.root().attribute(&doc, "d"), Some("e"));
    /// assert_eq!(doc.root().attribute(&doc, "f"), None);
    /// ```
    ///
    /// # Panics
    ///
    /// This method may panic if `name` is not a valid attribute name.
    pub fn attribute<'d>(&self, document: &'d Document, name: &str) -> Option<&'d str> {
        let attrs = self.attributes(document);

        attrs.get(&name.parse::<QName>().unwrap()).map(|x| &**x)
    }

    /// Set the value of an attribute on this element.
    ///
    /// ```
    /// # use qname::qname;
    /// let mut doc = xmlem::Document::new("root");
    /// doc.root().set_attribute(&mut doc, "a:b", "c");
    /// doc.root().set_attribute(&mut doc, "d", "e");
    /// assert_eq!(doc.to_string(), r#"<root a:b="c" d="e"/>"#);
    /// ```
    ///
    /// # Panics
    ///
    /// This method panics if `name` is not a valid attribute name.
    pub fn set_attribute(&self, document: &mut Document, name: &str, value: &str) {
        if !document.attrs.contains_key(self.0) {
            document.attrs.insert(self.0, Default::default());
        }

        let attrs = document.attrs.get_mut(self.0).unwrap();
        attrs.insert(name.parse().unwrap(), value.into());
    }

    /// Remove an attribute on this element.
    ///
    /// ```
    /// # use qname::qname;
    /// let mut doc = r#"<root a:b="c" d="e"/>"#.parse::<xmlem::Document>().unwrap();
    /// doc.root().remove_attribute(&mut doc, "a:b");
    /// doc.root().remove_attribute(&mut doc, "d");
    /// doc.root().remove_attribute(&mut doc, "f");
    /// assert_eq!(doc.to_string(), r#"<root/>"#);
    /// ```
    ///
    /// # Panics
    ///
    /// This method may panic if `name` is not a valid attribute name.
    pub fn remove_attribute(&self, document: &mut Document, name: &str) {
        if !document.attrs.contains_key(self.0) {
            return;
        }

        let attrs = document.attrs.get_mut(self.0).unwrap();
        attrs.shift_remove(&name.parse::<QName>().unwrap());
    }

    pub fn display(&self, document: &Document) -> String {
        let element = document.nodes.get(self.0).unwrap().as_element().unwrap();
        let mut s = Vec::<u8>::new();
        element
            .print(
                &mut s,
                &display::Config::default_pretty(),
                &display::State::new(document, true),
            )
            .expect("Invalid string somehow");
        String::from_utf8(s).expect("Invalid UTF-8")
    }

    pub fn walk<'d>(&self, doc: &'d Document) -> Box<dyn Iterator<Item = Element> + 'd> {
        walk_tree(doc, *self)
    }

    pub fn next_sibling_element(&self, doc: &Document) -> Option<Element> {
        let parent = match self.parent(doc) {
            Some(v) => v,
            None => return None,
        };

        let children = parent.children(doc);
        let mut index = children
            .iter()
            .position(|x| x == self)
            .expect("element has to be child of parent");
        index += 1;

        if index < children.len() {
            return Some(children[index]);
        }

        None
    }

    pub fn prev_sibling_element(&self, doc: &Document) -> Option<Element> {
        let parent = match self.parent(doc) {
            Some(v) => v,
            None => return None,
        };

        let children = parent.children(doc);
        let mut index = children
            .iter()
            .position(|x| x == self)
            .expect("element has to be child of parent");

        if index == 0 {
            return None;
        }
        index -= 1;

        if index == 0 {
            return None;
        }

        Some(children[index])
    }

    pub fn query_selector(&self, doc: &Document, selector: &Selector) -> Option<Element> {
        self.walk(doc).find(|x| selector.matches(doc, *x))
    }

    pub fn query_selector_all(&self, doc: &Document, selector: &Selector) -> Vec<Element> {
        self.walk(doc)
            .filter(|x| selector.matches(doc, *x))
            .collect()
    }
}

fn walk_tree<'a>(doc: &'a Document, element: Element) -> Box<dyn Iterator<Item = Element> + 'a> {
    let children = element.children(doc).to_vec();
    let mut index = 0usize;

    let mut last_child: Option<Box<dyn Iterator<Item = Element>>> = None;

    Box::new(std::iter::from_fn(move || {
        if let Some(iter) = last_child.as_mut() {
            if let Some(next) = iter.next() {
                return Some(next);
            } else {
                last_child = None;
            }
        }

        if index >= children.len() {
            return None;
        }

        let child = children[index];
        index += 1;

        last_child = Some(Box::new(walk_tree(doc, child)));
        Some(child)
    }))
}

static EMPTY_INDEXMAP: Lazy<IndexMap<QName, String>> = Lazy::new(IndexMap::new);
