use std::borrow::Borrow;
use std::hash::Hasher;

use cssparser::{CowRcStr, ParseError, SourceLocation};
use precomputed_hash::PrecomputedHash;
use qname::QName;
use selectors::attr::{AttrSelectorOperation, CaseSensitivity, NamespaceConstraint};
use selectors::context::{MatchingForInvalidation, NeedsSelectorFlags, QuirksMode, SelectorCaches};
use selectors::parser::{
    NonTSPseudoClass, ParseRelative, Parser, Selector as GenericSelector, SelectorImpl,
    SelectorList,
};
use selectors::parser::{PseudoElement, SelectorParseErrorKind};
use selectors::{self, matching, OpaqueElement};

use crate::{Document, Element};

#[derive(Debug, Clone)]
pub struct Selectors;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PrehashedString {
    val: String,
    hash: u32,
}

impl PrehashedString {
    fn as_str(&self) -> &str {
        &self.val
    }

    fn new(s: impl Into<String>) -> Self {
        let s = s.into();
        Self {
            hash: hash(&s),
            val: s,
        }
    }
}

fn hash(s: &str) -> u32 {
    let mut hasher = std::hash::DefaultHasher::new();
    std::hash::Hash::hash(&s, &mut hasher);
    hasher.finish() as u32
}

impl Borrow<String> for PrehashedString {
    fn borrow(&self) -> &String {
        &self.val
    }
}

impl PrecomputedHash for PrehashedString {
    fn precomputed_hash(&self) -> u32 {
        self.hash
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Value(PrehashedString);

impl Value {
    fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl cssparser::ToCss for Value {
    fn to_css<W>(&self, dest: &mut W) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        write!(dest, "{}", self.as_str())
    }
}

impl PrecomputedHash for Value {
    fn precomputed_hash(&self) -> u32 {
        self.0.precomputed_hash()
    }
}

impl From<&str> for Value {
    fn from(x: &str) -> Self {
        Value(PrehashedString::new(x))
    }
}

impl AsRef<str> for Value {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Borrow<String> for Value {
    fn borrow(&self) -> &String {
        &self.0.val
    }
}

impl NonTSPseudoClass for Value {
    type Impl = Selectors;

    fn is_active_or_hover(&self) -> bool {
        false
    }

    fn is_user_action_state(&self) -> bool {
        false
    }
}

impl PseudoElement for Value {
    type Impl = Selectors;
}

impl SelectorImpl for Selectors {
    type ExtraMatchingData<'a> = ();
    type AttrValue = Value;
    type Identifier = Value;
    type LocalName = Value;
    type NamespaceUrl = PrehashedString;
    type NamespacePrefix = Value;
    type BorrowedNamespaceUrl = String;
    type BorrowedLocalName = String;
    type NonTSPseudoClass = Value;
    type PseudoElement = Value;
}

#[derive(Debug, Clone)]
struct ElementRef<'a> {
    document: &'a Document,
    element: Element,
}

impl selectors::Element for ElementRef<'_> {
    type Impl = Selectors;

    fn opaque(&self) -> OpaqueElement {
        OpaqueElement::new(&self.element.0)
    }

    fn parent_element(&self) -> Option<Self> {
        self.element.parent(self.document).map(|e| ElementRef {
            document: self.document,
            element: e,
        })
    }

    fn parent_node_is_shadow_root(&self) -> bool {
        false
    }

    fn containing_shadow_host(&self) -> Option<Self> {
        None
    }

    fn is_pseudo_element(&self) -> bool {
        false
    }

    fn prev_sibling_element(&self) -> Option<Self> {
        self.element
            .prev_sibling_element(self.document)
            .map(|e| ElementRef {
                document: self.document,
                element: e,
            })
    }

    fn next_sibling_element(&self) -> Option<Self> {
        self.element
            .next_sibling_element(self.document)
            .map(|e| ElementRef {
                document: self.document,
                element: e,
            })
    }

    fn is_html_element_in_html_document(&self) -> bool {
        false
    }

    fn has_local_name(&self, local_name: &<Self::Impl as SelectorImpl>::BorrowedLocalName) -> bool {
        self.element.name(self.document) == local_name
    }

    fn has_namespace(&self, ns: &<Self::Impl as SelectorImpl>::BorrowedNamespaceUrl) -> bool {
        self.element.prefix(self.document) == Some(ns)
    }

    fn is_same_type(&self, other: &Self) -> bool {
        self.element.name(self.document) == other.element.name(other.document)
    }

    fn attr_matches(
        &self,
        ns: &NamespaceConstraint<&<Self::Impl as SelectorImpl>::NamespaceUrl>,
        local_name: &<Self::Impl as SelectorImpl>::LocalName,
        operation: &AttrSelectorOperation<&<Self::Impl as SelectorImpl>::AttrValue>,
    ) -> bool {
        let attrs = self.element.attributes(self.document);

        let qname = match ns {
            NamespaceConstraint::Any => QName::new_unchecked(local_name.as_ref()),
            NamespaceConstraint::Specific(ns) if ns.as_str() == "" => {
                QName::new_unchecked(local_name.as_str())
            }
            NamespaceConstraint::Specific(ns) => {
                QName::new_unchecked(&format!("{}:{}", ns.as_str(), local_name.as_str()))
            }
        };

        if let Some(val) = attrs.get(&qname) {
            operation.eval_str(val)
        } else {
            false
        }
    }

    fn match_non_ts_pseudo_class(
        &self,
        _pc: &<Self::Impl as SelectorImpl>::NonTSPseudoClass,
        _context: &mut selectors::context::MatchingContext<Self::Impl>,
    ) -> bool {
        false
    }

    fn match_pseudo_element(
        &self,
        _pe: &<Self::Impl as SelectorImpl>::PseudoElement,
        _context: &mut selectors::context::MatchingContext<Self::Impl>,
    ) -> bool {
        false
    }

    fn is_link(&self) -> bool {
        false
    }

    fn is_html_slot_element(&self) -> bool {
        false
    }

    fn has_id(
        &self,
        id: &<Self::Impl as SelectorImpl>::Identifier,
        case_sensitivity: CaseSensitivity,
    ) -> bool {
        match self.element.attribute(self.document, "id") {
            Some(x) => case_sensitivity.eq(x.as_bytes(), id.as_str().as_bytes()),
            None => false,
        }
    }

    fn has_class(
        &self,
        name: &<Self::Impl as SelectorImpl>::Identifier,
        case_sensitivity: CaseSensitivity,
    ) -> bool {
        match self.element.attribute(self.document, "class") {
            Some(x) => x
                .split_whitespace()
                .any(|x| case_sensitivity.eq(x.as_bytes(), name.as_str().as_bytes())),
            None => false,
        }
    }

    fn imported_part(
        &self,
        _name: &<Self::Impl as SelectorImpl>::Identifier,
    ) -> Option<<Self::Impl as SelectorImpl>::Identifier> {
        None
    }

    fn is_part(&self, _name: &<Self::Impl as SelectorImpl>::Identifier) -> bool {
        false
    }

    fn is_empty(&self) -> bool {
        self.element.children(self.document).is_empty()
    }

    fn is_root(&self) -> bool {
        self.document.root() == self.element
    }

    fn first_element_child(&self) -> Option<Self> {
        self.element
            .children(self.document)
            .into_iter()
            .next()
            .map(|child| Self {
                element: child,
                document: self.document,
            })
    }

    fn apply_selector_flags(&self, _flags: matching::ElementSelectorFlags) {}

    fn has_custom_state(&self, _name: &<Self::Impl as SelectorImpl>::Identifier) -> bool {
        false
    }

    fn add_element_unique_hashes(&self, _filter: &mut selectors::bloom::BloomFilter) -> bool {
        false
    }
}

struct TheParser;

impl<'i> Parser<'i> for TheParser {
    type Impl = Selectors;
    type Error = SelectorParseErrorKind<'i>;

    fn parse_non_ts_pseudo_class(
        &self,
        location: SourceLocation,
        name: CowRcStr<'i>,
    ) -> Result<Value, ParseError<'i, SelectorParseErrorKind<'i>>> {
        Err(
            location.new_custom_error(SelectorParseErrorKind::UnsupportedPseudoClassOrElement(
                name,
            )),
        )
    }
}

#[derive(Debug, Clone)]
struct SelectorInner(GenericSelector<Selectors>);

#[derive(Debug, Clone)]
pub struct Selector(Vec<SelectorInner>);

impl Selector {
    pub fn new(s: &str) -> Result<Selector, ParseError<SelectorParseErrorKind>> {
        let mut input = cssparser::ParserInput::new(s);
        match SelectorList::parse(
            &TheParser,
            &mut cssparser::Parser::new(&mut input),
            ParseRelative::No,
        ) {
            Ok(list) => Ok(Selector(
                list.slice().iter().cloned().map(SelectorInner).collect(),
            )),
            Err(e) => Err(e),
        }
    }

    /// Returns whether the given element matches this selector.
    #[inline]
    pub fn matches(&self, document: &Document, element: Element) -> bool {
        let mut cache = SelectorCaches::default();
        let mut context = matching::MatchingContext::new(
            matching::MatchingMode::Normal,
            None,
            &mut cache,
            QuirksMode::NoQuirks,
            NeedsSelectorFlags::No,
            MatchingForInvalidation::No,
        );
        self.0.iter().any(|s| {
            matching::matches_selector(
                &s.0,
                0,
                None,
                &ElementRef { document, element },
                &mut context,
            )
        })
    }
}
