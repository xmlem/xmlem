use qname::QName;

use crate::key::Node;

#[derive(Debug, Clone)]
pub(crate) enum NodeValue {
    Element(ElementValue),
    Text(String),
    CData(String),
    Comment(String),
    DocumentType(String),
}

#[derive(Debug, Clone)]
pub struct ElementValue {
    pub(crate) name: QName,
    pub(crate) children: Vec<Node>,
}

impl NodeValue {
    pub fn as_str(&self) -> Option<&str> {
        match self {
            NodeValue::Text(x)
            | NodeValue::CData(x)
            | NodeValue::Comment(x)
            | NodeValue::DocumentType(x) => Some(x),
            NodeValue::Element(_) => None,
        }
    }

    pub fn as_element(&self) -> Option<&ElementValue> {
        match self {
            NodeValue::Element(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_element_mut(&mut self) -> Option<&mut ElementValue> {
        match self {
            NodeValue::Element(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_document_type(&self) -> Option<&str> {
        match self {
            NodeValue::DocumentType(e) => Some(e),
            _ => None,
        }
    }
}
