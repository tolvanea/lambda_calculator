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
use AstNode::{Definition, Application, Symbol};

impl AstNode {
    fn fast_clone(&self) -> AstNode {
        match self {
            Definition(symbol, _, t) => Definition(symbol.clone(), Vec::new(), *t),
            Application(t1, t2) => Application(*t1, *t2),
            Symbol(symbol) => Symbol(symbol.clone()),
        }
    }
}

// TODO get rid of local arena


struct Ast {
    head: DefaultKey,
    t: SlotMap<DefaultKey, AstNode>,  // tree
}

impl Ast {
    fn new(source_code: &str) -> Ast {
        let re = Regex::new(r"([()])|(λ\s?[^()λ\s\.]+)\s?\.|([^()λ\s\.]+)").unwrap();
        let mut tokens = re.captures_iter(&source_code).map(|c| c.extract::<1>().1[0]).peekable();
        let mut ast = Ast {head: DefaultKey::null(), t: SlotMap::new()};
        let mut symbols = HashMap::<CompactString, Vec<Vec<DefaultKey>>>::new();
        ast.head = ast.parse(&mut tokens, &mut symbols, 0);
        ast
    }

    fn print(&self) {
        println!("{}", self.print_flat(self.head, true));
    }

    #[allow(dead_code)]
    fn print_flat(&self, node:DefaultKey, appl: bool) -> String {
        match self.t.get(node).unwrap() {
            Definition(s, _, t) => {
                let def = format!(
                    "λ{s}.{}",
                    self.print_flat(*t, false),
                );
                if appl {def} else {format!("({})", def)}
            }
            Application(t1, t2) => format!(
                "({} {})",
                self.print_flat(*t1, true),
                self.print_flat(*t2, true),
            ),
            Symbol(s) => format!("{s}")
        }
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
                symbols.entry(symbol.clone()).or_insert(Vec::new()).push(Vec::new());
                let sub_ast = self.parse(tokens, symbols, indt+1);
                let references = symbols.get_mut(&symbol).unwrap().pop().unwrap(); // Scope visibility
                let ast = Definition(symbol, references, sub_ast);
                println!("{}processed {}", " ".repeat(4*indt), token);
                self.t.insert(ast)
            }
            '(' => {
                let ast1 = self.parse(tokens, symbols, indt+1);
                let ast = match *tokens.peek().unwrap() {
                    ")" => {
                        ast1 // Only one expression: no need to wrap it
                    }
                    _ => {
                        let ast2 = Application(ast1, self.parse(tokens, symbols, indt+1));
                        println!("{}processed )", " ".repeat(4*indt));
                        self.t.insert(ast2)
                    }
                };
                assert_eq!(tokens.next(), Some(")"));
                ast
            }
            ')' => panic!("Syntax error ')' right before:\n{}", tokens.collect::<String>()),
            _ => {
                println!("{}was leaf )", " ".repeat(4*indt));
                let symbol: CompactString = token.into();
                let node = self.t.insert(Symbol(symbol.clone()));
                symbols.get_mut(&symbol)
                    .unwrap_or_else(|| panic!("Unknown symbol '{symbol}'"))
                    .last_mut().unwrap().push(node);
                node
            }
        }
    }

    fn beta_reduce(&mut self, node: DefaultKey, argument: Option<(DefaultKey, DefaultKey)>) -> bool {
        match self.t.get(node).unwrap().clone() {
            Definition(s, symbols, n) => {
                match argument {
                    None => self.beta_reduce(n, None),
                    Some((arg, parent)) => {
                        println!("D{s} {} : {}", self.print_flat(n, true), self.print_flat(arg, true));
                        for (i, reference) in symbols.iter().enumerate() {
                            println!("???");
                            let arg_copied = if i < symbols.len() - 1 {
                                let cloned = self.deep_clone(arg, &mut HashMap::new());
                                self.t.remove(cloned).unwrap() // useless allocation and deallocation :/
                            } else {
                                self.t.remove(arg).unwrap()
                            };
                            *self.t.get_mut(*reference).unwrap() = arg_copied;
                        } // TODO last item is unnecessary copy
                        *self.t.get_mut(parent).unwrap() = self.t.remove(n).unwrap();
                        self.t.remove(node).unwrap();
                        true
                    }
                }
            }
            Application(t1, t2) => {
                println!("A ({} : {})", self.print_flat(t1, true), self.print_flat(t2, true));
                self.beta_reduce(t1, Some((t2, node))) || self.beta_reduce(t2, None)
            },
            Symbol(s) => {
                println!("S{s}");
                false
            },
        }
    }

    fn deep_clone(
        &mut self,
        key: DefaultKey,
        symbols: &mut HashMap<CompactString, Vec<Vec<DefaultKey>>>,
    ) -> DefaultKey {
        match self.t.get(key).unwrap().fast_clone() {
            Definition(symbol, _, t) => {
                println!("D{symbol}");
                symbols.entry(symbol.clone()).or_insert(Vec::new()).push(Vec::new());
                let cloned_node = self.deep_clone(t, symbols);
                let references = symbols.get_mut(&symbol).unwrap().pop().unwrap(); // Scope visibility
                self.t.insert(Definition(symbol.clone(), references, cloned_node))
            }
            Application(t1, t2) => {
                println!("A");
                let a = Application(self.deep_clone(t1, symbols), self.deep_clone(t2, symbols));
                self.t.insert(a)
            }
            Symbol(symbol) => {
                println!("S{symbol}");
                let cloned = self.t.insert(Symbol(symbol.clone()));
                symbols.get_mut(&symbol).map(|n| n.last_mut().unwrap().push(cloned));
                cloned
            }
        }
    }
}




fn main() {
    //let mut sm = SlotMap::new();
    let true_fn = "λa.(λb.a)";
    let false_fn = "λa.(λb.b)";
    let and_nf = format!("λx.(λy.((x y) {false_fn}))");

    let one = "λa.a";
    let two = "λb.(b b)";
    let three = "λc.(c (c c))";
    let succ = "λn1.(λd.(d (n1 d)))";
    let times = format!("λn2.(λm.((m {succ}) n2))");
    //let input = format!("(λ x . ( λ y . ( x y ) ) (λ z . ( z )))");
    //let input = format!("(({and_nf} {true_fn}) {false_fn})");
    let input = format!("({succ} {two})");
    //let input = format!("(({times} {two}) {one})");

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
    ast.beta_reduce(ast.head, None);
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
