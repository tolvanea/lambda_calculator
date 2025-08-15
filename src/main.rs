use slotmap::{SlotMap, DefaultKey};
use regex::Regex;
use compact_str::CompactString;
use std::iter::Peekable;
use slotmap::Key;
use std::collections::{HashMap, HashSet};
use AstNode::{Definition, Application, Symbol};

type Symbols = HashMap<CompactString, Vec<(DefaultKey, Vec<DefaultKey>)>>;

fn null() -> DefaultKey {
    DefaultKey::null()
}

#[derive(Clone)]
enum AstNode {
    // Symbol, children symbols, child body
    Definition(CompactString, Vec<DefaultKey>, DefaultKey),
    // Left, right
    Application(DefaultKey, DefaultKey),
    // Symbol, defining node
    Symbol(CompactString, DefaultKey),
}

struct Ast {
    hat: DefaultKey, // Invisible dummy node above the head
    t: SlotMap<DefaultKey, AstNode>,  // tree
}

impl Ast {
    fn new(source_code: &str, print: bool) -> Ast {
        let re = Regex::new(r"([()])|(λ\s*[^()λ\.]+)\.|([^()λ\.\s\r\n]+)").unwrap();
        let mut tokens = re.captures_iter(&source_code).map(|c| c.extract::<1>().1[0]).peekable();
        let mut ast = Ast {t: SlotMap::new(), hat: null()};
        let mut symbols = Symbols::new();
        let head = ast.parse(&mut tokens, &mut symbols, print as usize);
        ast.hat = ast.t.insert(Definition("^".into(), Vec::new(), head));
        ast
    }

    fn head(&self) -> DefaultKey {
        match self.t.get(self.hat) {
            Some(Definition(_, _, head)) => *head,
            _ => panic!(),
        }
    }

    fn print(&self) {
        let mut symbols = Symbols::new();
        println!("{}", self.print_flat(self.head(), &mut symbols));
    }

    fn compute(&mut self, print: bool) {
        for i in 0..1000000 {
            if print {
                print!("{:<5}", i);
                self.print();
            }
            if !self.beta_reduce(self.head(), self.hat, None) {
                break
            }
        }
    }

    // fn debug(&self, node: DefaultKey) {
    //     use std::io::prelude::*;
    //     match self.t.get(node).unwrap() {
    //         Definition(s, symbols, t) => {
    //             print!("λ{s}[{}].(", symbols.len());
    //             std::io::stdout().flush().unwrap();
    //             for sn in symbols{
    //                 std::io::stdout().flush().unwrap();
    //                 match self.t.get(*sn).unwrap().fast_clone() {
    //                     Symbol(_s, br) => assert!(self.t.get(br).is_some()),
    //                     _ => panic!(),
    //                 }
    //             }
    //             self.debug(*t);
    //             print!(")");
    //             std::io::stdout().flush().unwrap();
    //         }
    //         Application(t1, t2) => {
    //             print!("(");
    //             self.debug(*t1);
    //             std::io::stdout().flush().unwrap();
    //             print!(" ");
    //             self.debug(*t2);
    //             print!(")");
    //             std::io::stdout().flush().unwrap();
    //         }
    //         Symbol(s, _) => print!("{s}")
    //     }
    // }

    #[allow(dead_code)]
    fn print_flat(&self, node: DefaultKey, symbols: &mut Symbols) -> String {
        match self.t.get(node).unwrap() {
            Definition(s, ss, t) => {
                // Invariant: all references are valid
                for sn in ss{
                    match self.t.get(*sn).unwrap() {
                        Symbol(_s, br) => assert!(self.t.get(*br).is_some()),
                        _ => panic!(),
                    }
                }
                let shadows = symbols.entry(s.clone()).or_insert(Vec::new());
                shadows.push((node, Vec::new()));
                let duplicates = shadows.len() - 1;
                let rest = self.print_flat(*t, symbols);
                symbols.get_mut(s).unwrap().pop();
                format!("λ{s}{}.{}", "'".repeat(duplicates), rest)
            }
            Application(t1, t2) => format!(
                "({} {})",
                self.print_flat(*t1, symbols),
                self.print_flat(*t2, symbols),
            ),
            Symbol(s, _) => {
                format!("{s}{}", "'".repeat(symbols.get(s).unwrap().len() - 1))
            }
        }
    }

    // Works together with create_leaf
    fn collect_symbols(
        &mut self,
        alloc: DefaultKey,
        child: DefaultKey,
        symbol: &CompactString,
        symbols: &mut Symbols,
    ) -> DefaultKey {
        let ss = symbols.get_mut(symbol).unwrap();
        let (_, references) = ss.pop().unwrap();
        if ss.is_empty() {
            symbols.remove(symbol);
        }
        match self.t.get_mut(alloc).unwrap() {
            Definition(_, refs, c) => {
                *refs = references;
                *c = child
            },
            _ => panic!(),
        };
        alloc
    }

    // Works together with collect_symbols
    fn create_leaf(
        &mut self,
        symbol: &CompactString,
        symbols: &mut Symbols,
        back_ref: Option<DefaultKey>
    ) -> DefaultKey {
        let alloc = self.t.insert(Symbol(symbol.clone(), null()));
        let (def_node, def_symbols) = match symbols.get_mut(symbol) {
            Some(s) => { // Symbol is found from local tree (parse / deep_clone)
                let (a, b) = s.last_mut().unwrap();
                (*a, b)
            },
            None => match back_ref { // Symbol is found from an outside context (deep_clone)
                Some(back_ref) => {
                    match self.t.get_mut(back_ref).unwrap() {
                        Definition(_, ss, _) => (back_ref, ss),
                        _ => panic!(),
                    }
                }
                None => panic!("Unknown symbol '{symbol}'")
            }
        };
        def_symbols.push(alloc);
        match self.t.get_mut(alloc).unwrap() {
            Symbol(_, p) => {*p = def_node},
            _ => panic!("Illegal operation")
        };
        alloc
    }

    fn parse<'a>(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = &'a str>>,
        symbols: &mut Symbols,
        indt: usize,
    ) -> DefaultKey {
        let token = tokens.next().expect("Closing parenthesis missing");
        let next_char = token.chars().next().unwrap();

        let indt1 = if indt == 0 { 0 } else { indt+1 };

        if next_char == 'λ' {
            let params = token[2..].trim().chars().filter(|c| !c.is_whitespace());

            let mut applications = Vec::new();
            for s in params {
                let mut symbol = CompactString::new(""); symbol.push(s); // Rust sucks,
                if indt > 0 { println!("{}λ{symbol}", " ".repeat(4*indt)); }
                let alloc = self.t.insert(Definition(symbol.clone(), Vec::new(), null()));
                symbols.entry(symbol.clone()).or_insert(Vec::new()).push((alloc, Vec::new()));
                applications.push((symbol, alloc));
            }

            let mut child = self.parse(tokens, symbols, indt1);

            for (symbol, alloc) in applications.iter().rev() {
                self.collect_symbols(*alloc, child, &symbol, symbols);
                child = *alloc;
            }
            child
        } else if next_char == '(' {
            if indt > 0 { println!("{}(", " ".repeat(4*indt)); }
            let mut left = self.parse(tokens, symbols, indt1);
            let mut arguments = Vec::new();

            while *tokens.peek().expect("Missing parenthesis ')'") != ")" {
                arguments.push(self.parse(tokens, symbols, indt1));
            }
            let ast = if arguments.is_empty() {
                left// Only one expression: no need to wrap it
            } else {
                for argument in arguments {
                    left = self.t.insert(Application(left, argument));
                }
                left
            };

            if indt > 0 { println!("{})", " ".repeat(4*indt)); }
            assert_eq!(tokens.next(), Some(")"));
            ast
        } else if next_char == '(' {
            panic!("Syntax error '(' right before:\n{}", tokens.collect::<String>())
        } else {
            let symbol: CompactString = token.into();
            if indt > 0 { println!("{}{symbol}", " ".repeat(4*indt)); }
            self.create_leaf(&symbol, symbols, None)
        }
    }

    fn beta_reduce(
        &mut self,
        node: DefaultKey,
        parent: DefaultKey,
        argument: Option<(DefaultKey, DefaultKey)>,
    ) -> bool {
        match self.t.get(node).unwrap().clone() {
            Definition(_, symbols, n) => {
                match argument {
                    None => {
                        self.beta_reduce(n, node, None)
                    }
                    Some((arg, grand_parent)) => {
                        for (i, reference) in symbols.iter().enumerate() {
                            let (arg_copied, arg_addr) = if i < symbols.len() - 1 {
                                let cloned = self.deep_clone(arg, &mut HashMap::new());
                                (self.t.remove(cloned).unwrap(), cloned) // alloc + dealloc :/
                            } else {
                                (self.t.remove(arg).unwrap(), arg)
                            };

                            match &arg_copied {
                                Definition(_, ss, _) => {
                                    for s in ss{
                                        match self.t.get_mut(*s).unwrap() {
                                            Symbol(_, br) => {*br = *reference}
                                            _ => panic!(),
                                        }
                                    }
                                }
                                Symbol(_, back_ref) => {
                                    match self.t.get_mut(*back_ref).unwrap() {
                                        Definition(_, ss, _) => {
                                            for s in ss {
                                                if *s == arg_addr {*s = *reference}
                                            }
                                        }
                                        _ => panic!(),
                                    }
                                }
                                _ => {}
                            }
                            *self.t.get_mut(*reference).unwrap() = arg_copied;
                        }
                        match self.t.get_mut(grand_parent).unwrap() {
                            Definition(_, _, t) => {*t = n}
                            Application(t1, t2) => {
                                if *t1 == parent {*t1 = n;} else {*t2 = n;}
                            }
                            _ => panic!(),
                        }
                        self.t.remove(node).unwrap();
                        self.t.remove(parent).unwrap();
                        true
                    }
                }
            }
            Application(t1, t2) => {
                let parn = Some((t2, parent));
                // Leftmost outermost reduction is guaranteed to yield beta-normal form, if exists
                self.beta_reduce(t1, node, parn) || self.beta_reduce(t2, node, None)
            },
            Symbol(_s, _back_ref) => {
                false
            },
        }
    }

    fn deep_clone(&mut self, key: DefaultKey, symbols: &mut Symbols) -> DefaultKey {
        match self.t.get(key).unwrap() {
            Definition(symbol, _, t) => {
                let (symbol, t) = (symbol.clone(), *t); // Rust iz funy laguane
                let alloc = self.t.insert(Definition(symbol.clone(), Vec::new(), null()));
                symbols.entry(symbol.clone()).or_insert(Vec::new()).push((alloc, Vec::new()));
                let child = self.deep_clone(t, symbols);
                self.collect_symbols(alloc, child, &symbol, symbols)
            }
            Application(t1, t2) => {
                let (t1, t2) = (*t1, *t2);
                let child1 = self.deep_clone(t1, symbols);
                let child2 = self.deep_clone(t2, symbols);
                self.t.insert(Application(child1, child2))
            }
            Symbol(symbol, back_ref) => {
                self.create_leaf(&symbol.clone(), symbols, Some(*back_ref))
            }
        }
    }
}




fn main() {
    let true_fn = "λab.a";
    let false_fn = "λab.b";
    let and_fn = format!("λxy.((x y) {false_fn})");

    let zero = "λzx.x";
    let one = "λax.(a x)";
    let two = "λbx.(b (b x))";
    let three = "λcz.(c (c (c z)))";

    let plus = "λnmfx.((n f) (m f x))";
    let times = "λnmf.(m (n f))";
    let exp = "λnm.(n m)";

    let succ = "λndx.(d (n d x))";
    let pred = "λnfx.(n λgh.(h (g f)) (λu.x) (λu.u))";

    let u = "λxy.(y (x x y))"; // Y combinator
    let if_0 = format!{"λn.((n λa.{false_fn}) {true_fn})"};

    let frac_f = format!{"λfn.({if_0} n {one} ({times} n (f ({pred} n))))"};
    let frac = format!{"({u} {u} {frac_f})"};

    let inputs = [
        ("false", format!("({and_fn} {true_fn} {false_fn})")),
        ("true", format!("({and_fn} {true_fn} {true_fn})")),
        ("true", format!("({if_0} {zero})")),
        ("2", format!("(({succ} {one}))")),
        ("2", format!("(({pred} {three}))")),
        ("5", format!("(({plus} {two}) {three})")),
        ("6", format!("(({times} {two}) {three})")),
        ("9", format!("(({exp} {two}) {three})")),
        ("6", format!("({frac} {three})")),
        ("astrophe", format!("(λ x y. (y x) λ y. y)")),
    ];
    //for (name, input) in [("muu", format!("λbx.(b (b x))"))] {
    for (name, input) in inputs {
        println!("{name}");
        println!("{input}");
        let mut ast = Ast::new(&input, false);
        ast.print();
        ast.compute(false);
        ast.print();
        println!("");
    }
}
