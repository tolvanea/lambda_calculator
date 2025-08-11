use slotmap::{SlotMap, DefaultKey};
use regex::Regex;
use compact_str::CompactString;
use std::iter::Peekable;
use slotmap::Key;
use std::collections::HashMap;

#[derive(Clone)]
enum AstNode {
    Definition(CompactString, Vec<DefaultKey>, DefaultKey), // Symbol, symbol refs, function body
    Application(DefaultKey, DefaultKey),
    Symbol(CompactString),
}

impl AstNode {
    #[allow(dead_code)]
    fn print_flat(&self, tree: &SlotMap<DefaultKey, AstNode>, appl: bool) -> String {
        match self {
            AstNode::Definition(s, _, t) => {
                let def = format!(
                    "λ{s}.{}",
                    tree.get(*t).unwrap().print_flat(tree, false),
                );
                if appl {def} else {format!("({})", def)}
            }
            AstNode::Application(t1, t2) => format!(
                "({} {})",
                tree.get(*t1).unwrap().print_flat(tree, true),
                tree.get(*t2).unwrap().print_flat(tree, true),
            ),
            AstNode::Symbol(s) => format!("{s}")
        }
    }

    #[allow(dead_code)]
    fn print(&self, tree: &SlotMap<DefaultKey, AstNode>, indt: usize) -> String {
        let indent = " ".repeat(4*indt);
        match self {
            AstNode::Definition(s, ss, t) => format!(
                "{indent}λ {s} [{}] (\n{}{indent})\n",
                ss.len(),
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

#[derive(Clone)]
struct Ast {
    head: DefaultKey,
    tree: SlotMap<DefaultKey, AstNode>,
}

impl Ast {
    fn new(source_code: &str) -> Ast {
        let re = Regex::new(r"([()])|(λ\s?[^()λ\s\.]+)\s?\.|([^()λ\s\.]+)").unwrap();
        let mut tokens = re.captures_iter(&source_code).map(|c| c.extract::<1>().1[0]).peekable();
        let mut ast = Ast {head: DefaultKey::null(), tree: SlotMap::new()};
        let mut symbols = HashMap::<CompactString, Vec<Vec<DefaultKey>>>::new();
        ast.head = ast.parse(&mut tokens, &mut symbols, 0);
        ast
    }

    fn parse<'a>(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = &'a str>>,
        symbols: &mut HashMap<CompactString, Vec<Vec<DefaultKey>>>,
        indt: usize,
    ) -> DefaultKey {
        let token = tokens.next().expect("Ran out of tokens");

        println!("{}token: '{}'", " ".repeat(4*indt), token);
        match token.chars().next().unwrap() {
            'λ' => {
                let symbol: CompactString = token[2..].trim_start().into();
                symbols.entry(symbol.clone())
                    .and_modify(|vec| vec.push(Vec::new()))
                    .or_insert(vec![Vec::new()]);
                let sub_ast = self.parse(tokens, symbols, indt+1);
                let references = symbols.get_mut(&symbol).unwrap().pop().unwrap(); // Scope visibility
                let ast = AstNode::Definition(symbol, references, sub_ast);
                println!("{}processed {}", " ".repeat(4*indt), token);
                self.tree.insert(ast)
            }
            '(' => {
                let ast1 = self.parse(tokens, symbols, indt+1);
                let ast = match *tokens.peek().unwrap() {
                    ")" => {
                        ast1 // Only one expression: no need to wrap it
                    }
                    _ => {
                        let ast2 = AstNode::Application(ast1, self.parse(tokens, symbols, indt+1));
                        println!("{}processed )", " ".repeat(4*indt));
                        self.tree.insert(ast2)
                    }
                };
                assert_eq!(tokens.next(), Some(")"));
                ast
            }
            ')' => panic!("Syntax error ')' right before:\n{}", tokens.collect::<String>()),
            _ => {
                println!("{}was leaf )", " ".repeat(4*indt));
                let symbol: CompactString = token.into();
                let node = self.tree.insert(AstNode::Symbol(symbol.clone()));
                match symbols.get_mut(&symbol) {
                    Some(vec) => vec.last_mut().unwrap().push(node),
                    None => panic!("Unknown symbol '{symbol}'"),
                }
                node
            }
        }
    }

    fn print(&self) {
        println!("{}", self.tree.get(self.head).unwrap().print_flat(&self.tree, true));
    }

    fn beta_reduce(&mut self, node: DefaultKey, argument: Option<(DefaultKey, DefaultKey)>) {
        let t = &mut self.tree;
        match t.get(node).unwrap().clone() {
            AstNode::Definition(_, symbols, n) =>
                match argument {
                    None => self.beta_reduce(n, None),
                    Some((arg, parent)) => {
                        for reference in symbols {
                            *t.get_mut(reference).unwrap() = t.get(arg).unwrap().clone();
                        }
                        *t.get_mut(parent).unwrap() = t.remove(n).unwrap();
                        t.remove(arg).unwrap();
                        t.remove(node).unwrap();
                    }
                }
            AstNode::Application(t1, t2) => self.beta_reduce(t1, Some((t2, node))),
            AstNode::Symbol(_) => (),
        }
    }
}




fn main() {
    //let mut sm = SlotMap::new();
    let true_fn = "λa.(λb.a)";
    let false_fn = "λa.(λb.b)";
    let and_nf = format!("λx.(λy.((x y) {false_fn}))");
    //let input = format!("(λ x . ( λ y . ( x y ) ) (λ z . ( z )))");
    let input = format!("(({and_nf} {true_fn}) {false_fn})");

    let mut ast = Ast::new(&input);
    println!("");
    println!("");
    println!("");
    println!("{input}");
    ast.print();
    ast.beta_reduce(ast.head, None);
    ast.print();
    ast.beta_reduce(ast.head, None);
    ast.print();
    ast.beta_reduce(ast.head, None);
    ast.print();
    ast.beta_reduce(ast.head, None);
    ast.print();
}
