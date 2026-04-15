use slotmap::new_key_type;

use crate::{element::Element, Document};

new_key_type! {
    pub(crate) struct DocKey;
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct Text(pub(crate) DocKey);

impl Text {
    pub fn as_str<'d>(&self, doc: &'d Document) -> &'d str {
        let node_value = &doc.nodes[self.0];
        node_value.as_str().unwrap()
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct CDataSection(pub(crate) DocKey);

impl CDataSection {
    pub fn as_str<'d>(&self, doc: &'d Document) -> &'d str {
        let node_value = &doc.nodes[self.0];
        node_value.as_str().unwrap()
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct ProcessingInstruction(pub(crate) DocKey);

impl ProcessingInstruction {
    pub fn as_str<'d>(&self, doc: &'d Document) -> &'d str {
        let node_value = &doc.nodes[self.0];
        node_value.as_str().unwrap()
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct Comment(pub(crate) DocKey);

impl Comment {
    pub fn as_str<'d>(&self, doc: &'d Document) -> &'d str {
        let node_value = &doc.nodes[self.0];
        node_value.as_str().unwrap()
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct DocumentType(pub(crate) DocKey);

#[derive(Debug, Copy, PartialEq, Eq, Clone)]
pub enum Node {
    Element(Element),
    Text(Text),
    CDataSection(CDataSection),
    ProcessingInstruction(ProcessingInstruction),
    Comment(Comment),
    DocumentType(DocumentType),
}

impl Node {
    pub(crate) fn as_key(self) -> DocKey {
        match self {
            Node::Element(e) => e.0,
            Node::Text(e) => e.0,
            Node::CDataSection(e) => e.0,
            Node::ProcessingInstruction(e) => e.0,
            Node::Comment(e) => e.0,
            Node::DocumentType(e) => e.0,
        }
    }

    pub fn as_text(self) -> Option<Text> {
        match self {
            Node::Text(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_element(self) -> Option<Element> {
        match self {
            Node::Element(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_document_type(self) -> Option<DocumentType> {
        match self {
            Node::DocumentType(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_cdata(self) -> Option<CDataSection> {
        match self {
            Node::CDataSection(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_comment(self) -> Option<Comment> {
        match self {
            Node::Comment(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_processing_instruction(self) -> Option<ProcessingInstruction> {
        match self {
            Node::ProcessingInstruction(e) => Some(e),
            _ => None,
        }
    }

    pub fn to_ordinal(&self) -> u8 {
        match self {
            Node::Element(_) => 0,
            Node::Text(_) => 1,
            Node::CDataSection(_) => 2,
            Node::Comment(_) => 3,
            Node::ProcessingInstruction(_) => 4,
            Node::DocumentType(_) => 5,
        }
    }
}
