pub mod display;
mod document;
mod element;
pub mod key;
mod select;
mod value;

pub use document::{Declaration, Document, ReadError};
pub use element::{Element, NewElement};
pub use key::Node;
pub use select::Selector;

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use qname::qname;

    use crate::select::Selector;

    use super::*;

    #[test]
    fn test() {
        use indexmap::IndexMap;

        use crate::document::Document;

        let mut doc = Document::new("root");

        let new_el = doc.root().append_new_element(
            &mut doc,
            NewElement {
                name: qname!("child"),
                attrs: Default::default(),
            },
        );
        new_el.append_new_element(
            &mut doc,
            NewElement {
                name: qname!("child2"),
                attrs: Default::default(),
            },
        );
        let mut attrs = IndexMap::new();
        attrs.insert(qname!("hello"), "yes".into());
        attrs.insert(qname!("another-thing"), "yes".into());

        let foo = new_el.append_new_element(
            &mut doc,
            NewElement {
                name: "with-child2".parse().unwrap(),
                attrs,
            },
        );
        foo.append_new_element(
            &mut doc,
            NewElement {
                name: "child3".parse().unwrap(),
                attrs: Default::default(),
            },
        );
        foo.append_new_element(
            &mut doc,
            NewElement {
                name: "child3".parse().unwrap(),
                attrs: Default::default(),
            },
        );
        foo.append_new_element(
            &mut doc,
            NewElement {
                name: "child3".parse().unwrap(),
                attrs: Default::default(),
            },
        );
        new_el.append_new_element(
            &mut doc,
            NewElement {
                name: "child2".parse().unwrap(),
                attrs: Default::default(),
            },
        );

        let _potato = doc.root().append_new_element(
            &mut doc,
            NewElement {
                name: "potato".parse().unwrap(),
                attrs: Default::default(),
            },
        );

        foo.parent(&mut doc)
            .unwrap()
            .remove_child(&mut doc, Node::Element(foo));

        println!("{}", doc);
    }

    #[test]
    fn smoke2() {
        let doc = Document::from_str(
            r#"<root xmlns:x="http://lol" someattr="true">lol <x:sparta/><sparta derp="9000"></sparta> </root>"#,
        ).unwrap();
        println!("{}", doc);
    }

    #[test]
    fn smoke3() {
        let input = r#"<俄语 լեզու="ռուսերեն">данные</俄语>"#;
        let doc = Document::from_str(input).unwrap();

        println!("{}", doc);
    }

    #[test]
    fn smoke4() {
        let input = "<root>ذ&amp;اكرة USB كبيرة السعة التخزينية (عصا، قرص ذاكرة USB)...</root>";
        let doc = Document::from_str(input).unwrap();

        println!("{}", doc);
    }

    #[test]
    fn smoke5() {
        let input = "<root>
            Text text &#x202d;text text
            &#x202e;text text &#x202d;text text
        </root>";
        let doc = Document::from_str(input).unwrap();

        println!("{}", doc);
    }

    #[test]
    fn clone() {
        let input = r#"<俄语 լեզու="ռուսերեն">данные</俄语>"#;
        let doc = Document::from_str(input).unwrap();
        let mut doc2 = doc.clone();

        let root = doc2.root();
        root.append_new_element(
            &mut doc2,
            NewElement {
                name: "lol".parse().unwrap(),
                attrs: Default::default(),
            },
        );

        println!("{}", doc);
        println!("{}", doc2);
    }

    #[test]
    fn long_attrs() {
        let input = r#"<root attribute1="potato potato potato"
            attribute2="potato potato potato"
            attribute3="potato potato potato"
            attribute4="potato potato potato"
        >
            <interesting attribute1="potato potato potato" attribute2="potato potato potato"
            />
            <another-one/>
        </root>
        "#;
        let doc = Document::from_str(input).unwrap();
        println!("{:#4.120}", doc);
        println!("{:#2.60}", doc);
        println!("{:#1.400}", doc);
    }

    #[test]
    fn hmm() {
        let input = "<?xml version=\"1.1\" ?>some random text<![CDATA[<hahaha>]]><!DOCTYPE root ahh ahhhh><!-- pre --><root/><!-- comment --> some other text";
        let doc = Document::from_str(input).unwrap();
        println!("{:#}", doc);
    }

    #[test]
    fn after() {
        let input = "<root><a/><b/><c/><d/></root>";
        let mut doc = Document::from_str(input).unwrap();

        let b = doc
            .root()
            .query_selector(&doc, &Selector::new("b").unwrap())
            .unwrap();
        b.append_new_element_after(&mut doc, ("potato", [("hihi", "oij")]));

        let d = doc
            .root()
            .query_selector(&doc, &Selector::new("d").unwrap())
            .unwrap();
        d.append_new_element_after(&mut doc, ("potato", [("hihi", "oij")]));
        println!("{:#}", doc);
    }

    #[test]
    fn after2() {
        let input = r#"<merge xmlns:latin="http://schemas.android.com/apk/res-auto">
            <include latin:keyboardLayout="@xml/key_styles_common" />
            <include latin:keyboardLayout="@xml/row_qwerty4" />
        </merge>"#;
        let mut doc = Document::from_str(input).unwrap();

        let include_selector = Selector::new("include").expect("this selector is fine");
        let rows_include = doc
            .root()
            .query_selector(&mut doc, &include_selector)
            .expect("there should be an include");

        let row_append = rows_include.append_new_element_after(
            &mut doc,
            NewElement {
                name: qname!("Row"),
                attrs: [].into(),
            },
        );

        row_append.append_new_element(
            &mut doc,
            NewElement {
                name: qname!("include"),
                attrs: [
                    (qname!("latin:keyboardLayout"), "@xml/potato".to_string()),
                    (qname!("latin:keyWidth"), "8.18%p".to_owned()),
                ]
                .into(),
            },
        );
        let row_append = row_append.append_new_element_after(
            &mut doc,
            NewElement {
                name: qname!("Row"),
                attrs: [].into(),
            },
        );

        row_append.append_new_element(
            &mut doc,
            NewElement {
                name: qname!("include"),
                attrs: [
                    (qname!("latin:keyboardLayout"), "@xml/potato".to_string()),
                    (qname!("latin:keyWidth"), "8.18%p".to_owned()),
                ]
                .into(),
            },
        );
        println!("{:#}", doc);
    }

    #[test]
    fn set_text() {
        let input = "<root><a/></root>";
        let mut doc = Document::from_str(input).unwrap();

        doc.root().set_text(&mut doc, "potato");

        println!("{:#}", doc);
    }

    #[test]
    fn double_use() {
        let input = "<root><a/></root>";
        let mut doc = Document::from_str(input).unwrap();

        let a = doc
            .root()
            .query_selector(&doc, &Selector::new("a").unwrap())
            .unwrap();
        doc.root().remove_child(&mut doc, Node::Element(a));
        assert_eq!(a.parent(&doc), None);

        let inner = doc.root().append_new_element(
            &mut doc,
            NewElement {
                name: qname!("test"),
                attrs: Default::default(),
            },
        );

        inner.append_element(&mut doc, a);
        println!("{:#}", doc);
    }

    #[test]
    fn selector() {
        let input =
            r#"<strings><string name="english_ime_name">Giella Keyboard</string></strings>"#;
        let doc = Document::from_str(input).unwrap();

        let sel = Selector::new(r#"string[name="english_ime_name"]"#).unwrap();
        let _el = doc.root().query_selector(&doc, &sel).unwrap();
    }

    #[test]
    fn non_root_empty_element_name() {
        let input = r#"<root><elem/><x:elem/></root>"#;
        let doc = Document::from_str(input).unwrap();

        let nq_elem = doc.root().children(&doc)[0];
        assert_eq!(nq_elem.qname(&doc).namespace(), None);
        assert_eq!(nq_elem.prefix(&doc), None);
        assert_eq!(nq_elem.qname(&doc).local_part(), "elem");
        assert_eq!(nq_elem.name(&doc), "elem");

        let q_elem = doc.root().children(&doc)[1];
        assert_eq!(q_elem.qname(&doc).namespace(), Some("x"));
        assert_eq!(q_elem.prefix(&doc), Some("x"));
        assert_eq!(q_elem.qname(&doc).local_part(), "elem");
        assert_eq!(q_elem.name(&doc), "x:elem");
    }

    #[test]
    fn non_root_non_empty_element_name() {
        let input = r#"<root><elem></elem><x:elem></x:elem></root>"#;
        let doc = Document::from_str(input).unwrap();

        let nq_elem = doc.root().children(&doc)[0];
        assert_eq!(nq_elem.qname(&doc).namespace(), None);
        assert_eq!(nq_elem.prefix(&doc), None);
        assert_eq!(nq_elem.qname(&doc).local_part(), "elem");
        assert_eq!(nq_elem.name(&doc), "elem");

        let q_elem = doc.root().children(&doc)[1];
        assert_eq!(q_elem.qname(&doc).namespace(), Some("x"));
        assert_eq!(q_elem.prefix(&doc), Some("x"));
        assert_eq!(q_elem.qname(&doc).local_part(), "elem");
        assert_eq!(q_elem.name(&doc), "x:elem");
    }

    #[test]
    fn set_attribute() {
        let mut doc = Document::from_str("<foo>").unwrap();
        doc.root().set_attribute(&mut doc, "bar", "baz");
        assert_eq!(doc.root().attribute(&doc, "bar"), Some("baz"));
    }

    #[test]
    fn pretty_minimizes_whitespace() {
        let doc = Document::from_str("<text>\n    Actual Output\n    </text>").unwrap();
        assert_eq!(doc.to_string_pretty(), "<text>\n  Actual Output\n</text>\n");
    }

    #[test]
    fn non_pretty_preserves_whitespace() {
        const EXACT_XML: &str = "<text>\t  \n Actual \n \t Output   \t\n  </text>";
        let doc = Document::from_str(EXACT_XML).unwrap();
        assert_eq!(doc.to_string(), EXACT_XML);
    }

    #[test]
    fn accepts_pi_before_root() {
        Document::from_str(r#"<?xml-stylesheet href="style.css" type="text/css"?><root/>"#)
            .unwrap();
    }

    fn parse_buffer(buf: &[u8]) -> Result<Document, ReadError> {
        Document::from_reader(std::io::Cursor::new(buf))
    }

    #[test]
    fn ignored_invalids() {
        parse_buffer(b"<?xml version=\"\xA1\"?><root/>").unwrap();
        parse_buffer(b"<?xml other?><root/>").unwrap();
        parse_buffer(b"<?xml version=\"1.1\" standalone=\"\xA1\"?><root/>").unwrap();
        parse_buffer(b"<?xml version=\"1.1\" encoding=\"\xA1\"?><root/>").unwrap();
    }

    #[test]
    fn erroring_invalids() {
        parse_buffer(b"").unwrap_err();
        parse_buffer(b"</root>").unwrap_err();
        parse_buffer(b"<!DOCTYPE a=\"&\"><root/>").unwrap_err();
        parse_buffer(b"<!DOCTYPE \xA1><root/>").unwrap_err();
        parse_buffer(b"&").unwrap_err();
        parse_buffer(b"<!-- & -->").unwrap_err();
        parse_buffer(b"<\xA1/>").unwrap_err();
        parse_buffer(b"<\x00/>").unwrap_err();
        parse_buffer(b"<root a=\"&\"/>").unwrap_err();
        parse_buffer(b"<root a=\"\xA1\"/>").unwrap_err();
        parse_buffer(b"<root \xA1=\"\"/>").unwrap_err();
        parse_buffer(b"<root><\xA1/></root>").unwrap_err();
        parse_buffer(b"<root><\x00/></root>").unwrap_err();
        parse_buffer(b"<root><elem a=\"\xA1\"/></root>").unwrap_err();
        parse_buffer(b"<root><elem a=\"&\"/></root>").unwrap_err();
        parse_buffer(b"<root><elem \xA1=\"\"/></root>").unwrap_err();
        parse_buffer(b"<root><elem \x00=\"\"/></root>").unwrap_err();
        parse_buffer(b"<root><\xA1></\xA1></root>").unwrap_err();
        parse_buffer(b"<root><\x00></\x00></root>").unwrap_err();
        parse_buffer(b"<root><elem a=\"\xA1\"></elem></root>").unwrap_err();
        parse_buffer(b"<root><elem a=\"&\"></elem></root>").unwrap_err();
        parse_buffer(b"<root><elem \xA1=\"\"></elem></root>").unwrap_err();
        parse_buffer(b"<root><elem \x00=\"\"></elem></root>").unwrap_err();
        parse_buffer(b"<a <=\"\"/>").unwrap_err();
    }
}
