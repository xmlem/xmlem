# xmlem

XML DOM manipulation for Rust.

## Quickstart

```rust
let mut doc = Document::from_str("<root><potato /></root>").unwrap();
let root = doc.root();

let potato = root.query_selector(&doc, Selector::new("potato").unwrap()).unwrap();
potato.append_new_element(&mut doc, (
    "wow",
    [
        ("easy", "true"),
        ("x", "200"),
        ("a-null", "\0"),
    ],
));

let decl = Declaration::v1_1();
doc.set_declaration(Some(decl));
doc.set_doctype(Some("not-html"));

println!("{}", doc.to_string_pretty());

/*
Prints:

<?xml version="1.1" encoding="utf-8" ?>
<!DOCTYPE not-html>
<root>
  <potato>
    <wow easy="true" x="200" a-null="&#x0000;" />
  </potato>
</root>
*/
```

You can run this example with `cargo run --example readme`, and see the `examples/readme.rs` file.

## Projects using xmlem

- [kbdgen](https://github.com/divvun/kbdgen): a keyboard layout generation tool used by minority and indigenous language communities
- [xml-pretty](https://github.com/xmlem/xml-pretty): a command line XML prettifier

## License

This project is licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

