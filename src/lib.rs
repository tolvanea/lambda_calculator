use slotmap::{SlotMap, DefaultKey};
use regex::Regex;
use compact_str::CompactString;
use std::iter::Peekable;
use slotmap::Key;
use std::collections::HashMap;
use AstNode::{Definition, Application, Symbol};

use wasm_bindgen::prelude::*;

type Symbols = HashMap<CompactString, Vec<(DefaultKey, Vec<DefaultKey>)>>;

#[wasm_bindgen]
pub fn process_input(input: &str) -> String {
    Ast::read_string_and_compute(input, true)
}

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
    bindings: HashMap<CompactString, DefaultKey>,
    t: SlotMap<DefaultKey, AstNode>,  // tree
}

impl Ast {
    fn read_string_and_compute(source_code: &str, debug_parsing: bool) -> String {
        let mut ast = Ast {t: SlotMap::new(), bindings:HashMap::new(), hat: null()};
        ast.read_source_code(source_code, debug_parsing);
        ast.compute_to_string()
    }

    fn head(&self) -> DefaultKey {
        match self.t.get(self.hat) {
            Some(Definition(_, _, head)) => *head,
            _ => panic!(),
        }
    }

    fn compute_to_string(&mut self) -> String {
        use std::fmt::Write;
        let mut symbols = Symbols::new();
        let mut out = format!("{:<5} {}\n", 0, self.print_flat(self.head(), &mut symbols));
        for i in 1..1000000 {
            let mut symbols = Symbols::new();
            if !self.beta_reduce(self.head(), self.hat, None) {
                break
            }
            write!(&mut out, "{:<5} {}\n", i, self.print_flat(self.head(), &mut symbols)).unwrap();
        }
        out
    }

    // symbols is only for counting astrophes ', and takes &mut only for internal book keeping
    fn print_flat(&mut self, node: DefaultKey, symbols: &mut Symbols) -> String {
        // Due to rust's borrow checker, this function is obsfuscated
        let mut symbol2 = CompactString::new("");
        let out = match self.t.get_mut(node).unwrap() {
            Definition(s, _, t) => {
                let t = *t;
                let shadows = symbols.entry(s.clone()).or_insert(Vec::new());
                shadows.push((node, Vec::new()));
                symbol2 = format!("{s}{}", "'".repeat(shadows.len() - 1)).into();
                let symbol_with_astrophes = symbol2.clone();
                // Temporarily overwrite symbol name for children
                std::mem::swap(s, &mut symbol2);
                let rest = self.print_flat(t, symbols);
                format!("λ{symbol_with_astrophes}.{}", rest)
            }
            Application(t1, t2) => {
                let t1 = *t1; // Yes, borrow checker is this stupid
                let t2 = *t2;
                format!(
                    "({} {})",
                    self.print_flat(t1, symbols),
                    self.print_flat(t2, symbols),
                )
            }
            Symbol(_, backref) => {
                let backref = *backref;
                match self.t.get(backref).unwrap() {
                    Definition(s, _, _) => format!("{s}"),
                    _ => panic!(),
                }
            }
        };
        // Return temporal symbol overwrite back to normal. Borrow checker wants it separate.
        match self.t.get_mut(node).unwrap() {
            Definition(s, _, _) => {
                std::mem::swap(s, &mut symbol2);
                symbols.get_mut(s).unwrap().pop();
            }
            _ => ()
        }
        out
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
                None => { // Replace symbol with definition. Executed only when parsing
                    match self.bindings.get(symbol) {
                        Some(ast) => {
                            self.t.remove(alloc); // Useless alloc-dealloc :/
                            return self.deep_clone(*ast, &mut HashMap::new())
                        }
                        None => panic!("Unknown symbol '{symbol}'"),
                    }
                }
            }
        };
        def_symbols.push(alloc);
        match self.t.get_mut(alloc).unwrap() {
            Symbol(_, p) => {*p = def_node},
            _ => panic!("Illegal operation")
        };
        alloc
    }

    fn parse(&mut self, source_code: &str, print: bool) -> DefaultKey {
        let mut symbols = Symbols::new();
        let re = Regex::new(r"([()])|(λ\s*[^()λ\.]+)\.|([^()λ\.\s\r\n]+)").unwrap();
        let mut tokens = re.captures_iter(&source_code).map(|c| c.extract::<1>().1[0]).peekable();
        self.parse_rec(&mut tokens, &mut symbols, print as usize)
    }

    fn parse_rec<'a>(
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

            let mut child = self.parse_rec(tokens, symbols, indt1);

            for (symbol, alloc) in applications.iter().rev() {
                self.collect_symbols(*alloc, child, &symbol, symbols);
                child = *alloc;
            }
            child
        } else if next_char == '(' {
            if indt > 0 { println!("{}(", " ".repeat(4*indt)); }
            let mut left = self.parse_rec(tokens, symbols, indt1);
            let mut arguments = Vec::new();

            while *tokens.peek().expect("Missing parenthesis ')'") != ")" {
                arguments.push(self.parse_rec(tokens, symbols, indt1));
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
                                            // Deep cloned symbol has been already pushed to ss
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
                        if symbols.is_empty() {
                            self.remove(arg) // No replacements, delete the whole argument
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

    fn remove(&mut self, key: DefaultKey) {
        match self.t.get(key).unwrap() {
            Definition(_, _, t) => {
                self.remove(*t);
            }
            Application(t1, t2) => {
                let (t1, t2) = (*t1, *t2);  // Rust being rust
                self.remove(t1);
                self.remove(t2);
            }
            Symbol(_, back_ref) => {
                match self.t.get_mut(*back_ref).unwrap() {
                    Definition(_, ss, _) => {
                        ss.iter()
                            .position(|s| *s==key)
                            .map(|pos| ss.swap_remove(pos));
                    }
                    _ => panic!(),
                }
            },
        }
        self.t.remove(key).unwrap();
    }


    fn read_source_code(&mut self, source_code: &str, print: bool) {
        let mut position = 0;
        for line_raw in source_code.split_inclusive('\n') {
            // Remove comments
            let line = match line_raw.find("#") {
                Some(n) => &line_raw[0..n].trim(),
                None => line_raw.trim()
            };
            if line == "" {
                position += line_raw.len();
                continue
            }
            let (variable_name, the_rest) = match line.find("=") {
                Some(n) => (line[..n].trim(), line[n+1..].trim()),
                None => {
                    if line.trim() == "in" {
                        position += line_raw.len();
                        break
                    } else if self.bindings.is_empty() {
                        break
                    } else {
                        panic!("Syntax error on line:\n{line}\nNo assignment \"=\" found")
                    }
                }
            };
            assert!(
                variable_name.chars().all(|c| !c.is_whitespace() && c != 'λ'),
                "Can not assign to '{variable_name}'"
            );
            position += line_raw.len();

            if print {println!("{} =", variable_name);}
            let body = self.parse(&the_rest, print);
            self.bindings.insert(variable_name.into(), body);
        }

        let last_lambda_expression = source_code[position..].trim();
        let head = self.parse(last_lambda_expression, print);
        self.hat = self.t.insert(Definition("^".into(), Vec::new(), head));
    }
}

#[test]
fn test() {
    let inn = "AA = λab.a\n
BB = λab.b\n
and = λxy.(x y BB)\n
in\n
(and AA BB)".to_string();
    Ast::read_string_and_compute(&inn, true);
}
