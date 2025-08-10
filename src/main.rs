use slotmap::{SlotMap, DefaultKey};
use regex::Regex;
use compact_str::CompactString;
use std::iter::Peekable;

enum Ast {
    Definition(CompactString, DefaultKey),
    Application(DefaultKey, DefaultKey),
    Expression(DefaultKey),
    Symbol(CompactString),
}

impl Ast {
    fn print(&self, tree: &SlotMap<DefaultKey, Ast>, indt: usize) -> String {
        let indent = " ".repeat(4*indt);
        match self {
            Ast::Definition(s, t) => format!(
                "{indent}λ {s} (\n{}{indent})\n",
                tree.get(*t).unwrap().print(tree, indt + 1),
            ),
            Ast::Application(t1, t2) => format!(
                "{indent}(\n{}{}{indent})\n",
                tree.get(*t1).unwrap().print(tree, indt + 1),
                tree.get(*t2).unwrap().print(tree, indt + 1),
            ),
            Ast::Expression(t) => format!(
                "{}",
                tree.get(*t).unwrap().print(tree, indt),
            ),
            Ast::Symbol(s) => format!("{indent}{s}\n")
        }
    }
}

fn parse<'a>(
    tokens: &mut Peekable<impl Iterator<Item = &'a str>>,
    tree: &mut SlotMap<DefaultKey, Ast>,
    indt: usize,
) -> DefaultKey {
    let token = tokens.next().expect("Ran out of tokens");

    println!("{}token: '{}'", " ".repeat(4*indt), token);

    let parsed = match token.chars().next().unwrap() {
        'λ' => {
            let ast = Ast::Definition(token[2..].into(), parse(tokens, tree, indt+1));
            println!("{}processed {}", " ".repeat(4*indt), token);
            ast
        }
        '(' => {
            let ast1 = parse(tokens, tree, indt+1);
            let ast3 = match *tokens.peek().unwrap() {
                ")" => Ast::Expression(ast1),
                _ => Ast::Application(ast1, parse(tokens, tree, indt+1)),
            };
            assert_eq!(tokens.next(), Some(")"));
            println!("{}processed )", " ".repeat(4*indt));
            ast3
        }
        ')' => panic!("Syntax error"),
        _ => {
            println!("{}was leaf )", " ".repeat(4*indt));
            Ast::Symbol(token.into())
        }

    };
    tree.insert(parsed)

}


fn main() {
    //let mut sm = SlotMap::new();
    let re = Regex::new(r"([()])|(λ\s?[^()λ\.]+\s?)\.|([^()λ\s\.]+)").unwrap();
    //let True = "λa.(λb.(a))"
    let input = "(λ x . ( λ y . ( x y ) ) (λ zzz . ( zzz )))";
    let mut tokens = re.captures_iter(input).map(|c| c.extract::<1>().1[0]).peekable();
    let mut tree = SlotMap::new();

    let ast = parse(&mut tokens, &mut tree, 0);
    println!("{}", tree.get(ast).unwrap().print(&tree, 0));
}
