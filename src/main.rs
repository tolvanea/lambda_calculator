use slotmap::{SlotMap, DefaultKey};
use regex::Regex;
use compact_str::CompactString;
use std::iter::Peekable;
use slotmap::Key;

enum AstNode {
    Definition(CompactString, DefaultKey),
    Application(DefaultKey, DefaultKey),
    Symbol(CompactString),
}

impl AstNode {
    fn print(&self, tree: &SlotMap<DefaultKey, AstNode>, indt: usize) -> String {
        let indent = " ".repeat(4*indt);
        match self {
            AstNode::Definition(s, t) => format!(
                "{indent}λ {s} (\n{}{indent})\n",
                tree.get(*t).unwrap().print(tree, indt + 1),
            ),
            AstNode::Application(t1, t2) => format!(
                "{indent}(\n{}{}{indent})\n",
                tree.get(*t1).unwrap().print(tree, indt + 1),
                tree.get(*t2).unwrap().print(tree, indt + 1),
            ),
            AstNode::Symbol(s) => format!("{indent}{s}\n")
        }
    }
}

struct Ast {
    head: DefaultKey,
    tree: SlotMap<DefaultKey, AstNode>,
}

impl Ast {
    fn new(source_code: &str) -> Ast {
        let re = Regex::new(r"([()])|(λ\s?[^()λ\.]+\s?)\.|([^()λ\s\.]+)").unwrap();
        let mut tokens = re.captures_iter(&source_code).map(|c| c.extract::<1>().1[0]).peekable();
        let mut ast = Ast {head: DefaultKey::null(), tree: SlotMap::new()};
        ast.head = ast.parse(&mut tokens, 0);
        ast
    }

    fn parse<'a>(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = &'a str>>,
        indt: usize,
    ) -> DefaultKey {
        let token = tokens.next().expect("Ran out of tokens");

        println!("{}token: '{}'", " ".repeat(4*indt), token);

        let parsed = match token.chars().next().unwrap() {
            'λ' => {
                let ast = AstNode::Definition(token[2..].into(), self.parse(tokens, indt+1));
                println!("{}processed {}", " ".repeat(4*indt), token);
                ast
            }
            '(' => {
                let ast1 = self.parse(tokens, indt+1);
                let ast3 = match *tokens.peek().unwrap() {
                    ")" => {
                        assert_eq!(tokens.next(), Some(")"));
                        return ast1 // Only one expression: no need to wrap it
                    }
                    _ => AstNode::Application(ast1, self.parse(tokens, indt+1)),
                };
                assert_eq!(tokens.next(), Some(")"));
                println!("{}processed )", " ".repeat(4*indt));
                ast3
            }
            ')' => panic!("Syntax error"),
            _ => {
                println!("{}was leaf )", " ".repeat(4*indt));
                AstNode::Symbol(token.into())
            }

        };
        self.tree.insert(parsed)
    }

    fn print(&self) {
        println!("{}", self.tree.get(self.head).unwrap().print(&self.tree, 0));
    }
}


// fn beta_reduce(
//     tree: &mut SlotMap<DefaultKey, AstNode>,
// )


fn main() {
    //let mut sm = SlotMap::new();
    let true_fn = "λa.(λb.a)";
    let false_fn = "λa.(λb.b)";
    let and_nf = format!("λx.(λy.((x y) {false_fn}))");
    //let input = "(λ x . ( λ y . ( x y ) ) (λ zzz . ( zzz )))";
    let input = format!("(({and_nf} {true_fn}) {false_fn})");
    println!("{input}");
    let ast = Ast::new(&input);
    ast.print();
}
