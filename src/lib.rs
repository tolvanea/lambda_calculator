use slotmap::{SlotMap, DefaultKey};
use regex::Regex;
use compact_str::CompactString;
use std::iter::Peekable;
use slotmap::Key;
use std::collections::HashMap;
use std::fmt::Write as _;


use wasm_bindgen::prelude::*;

//                    symbol name, symbol defining node, list of children
type Symbols = HashMap<CompactString, Vec<(DefaultKey, Vec<DefaultKey>)>>;
type Res<T> = Result<T, ()>;

#[wasm_bindgen]
pub fn process_input(source_code: &str, debug_parsing: bool) -> Result<String, JsError> {
    Ast::read_string_and_compute(source_code, debug_parsing).map_err(|e| JsError::new(&e))
}

fn null() -> DefaultKey {
    DefaultKey::null()
}

// Colors of definitions
const BODY_COLORS: [&str; 5] = [
    "#045893",
    "#DB6100",
    "#108010",
    "#B40C0D",
    "#74499C",
];

const PARENTHESIS_COLORS: [&str; 8] = [
    "#000000",
    "#C158A0",
    "#9A9C07",
    "#616161",
    "#009DAC",
    "#6D392E",
    "#16AB16",
    "#DB2800",
];


#[derive(Clone)]
enum AstNode {
    // Symbol, Children symbols, Child body, body color
    Definition(CompactString, Vec<DefaultKey>, DefaultKey, usize),
    // Left, right, parenthesis color, body color
    Application(DefaultKey, DefaultKey, usize, usize),
    // Color
    Symbol(DefaultKey),
}
use AstNode::{Definition, Application, Symbol};

struct Ast {
    hat: DefaultKey, // Invisible dummy node above the head
    bindings: HashMap<CompactString, DefaultKey>,
    t: SlotMap<DefaultKey, AstNode>,  // tree
}

impl Ast {
    fn read_string_and_compute(source_code: &str, debug_parsing: bool) -> Result<String, String> {
        let mut ast = Ast {t: SlotMap::new(), bindings:HashMap::new(), hat: null()};
        let mut output = String::new();
        match ast.read_source_code(source_code, debug_parsing, &mut output) {
            Ok(_) => {
                writeln!(output, "\n").unwrap();
                match ast.compute_to_string(&mut output) {
                    Ok(_) => Ok(output),
                    Err(_) => Err(output),
                }
            }
            Err(_) => {
                output.replace_range(..0, "\n"); // Javascript adds "Error: " to the string :(
                Err(output)
            }
        }
    }

    fn head(&self) -> DefaultKey {
        match self.t.get(self.hat) {
            Some(Definition(_, _, head, _)) => *head,
            _ => panic!(),
        }
    }

    fn compute_to_string(&mut self, output: &mut String) -> Res<()> {
        let mut symbols = Symbols::new();
        writeln!(output, "{:<5} {}", 0, self.print_flat(self.head(), &mut symbols)).unwrap();
        let mut counter = 1;
        let succ = loop  {
            let mut symbols = Symbols::new();
            if !self.beta_reduce(self.head(), self.hat, None, output)? { // Normal form is found
                // In case the result was not printed on last round, print it now
                if (100 < counter && counter <= 1000 && (counter-1) % 5 != 0)
                    || (1000 < counter && (counter-1) % 20 != 0)
                {
                    writeln!(
                        output,
                        "{counter:<5} {}",
                        self.print_flat(self.head(), &mut symbols)
                    ).unwrap();
                }
                break true

            }
            if counter == 100 {
                writeln!(output, "Printing every 5th line to reduce output").unwrap();
            } else if counter == 1000 {
                writeln!(output, "Printing every 20th line to reduce output").unwrap();
            }
            if counter < 100 || (counter < 1000 && counter % 5 == 0) || (counter % 20 == 0) {
                writeln!(
                    output,
                    "{counter:<5} {}",
                    self.print_flat(self.head(), &mut symbols)
                ).unwrap();
            }
            if counter >= 10000 || self.t.len() > 5000 {
                break false
            }
            counter += 1;
        };
        if succ {
            Ok(())
        } else {
            writeln!(output, "The program does not seem to halt, terminating it").unwrap();
            Err(())
        }
    }

    // symbols is only for counting astrophes ', and takes &mut only for internal book keeping
    fn print_flat(&mut self, node: DefaultKey, symbols: &mut Symbols) -> String {
        // Due to rust's borrow checker, this function is obsfuscated
        let mut symbol2 = CompactString::new("");
        let out = match self.t.get_mut(node).unwrap() {
            Definition(s, _, t, body_color) => {
                let t = *t;
                let body_color = BODY_COLORS[*body_color];
                let shadows = symbols.entry(s.clone()).or_default();
                shadows.push((node, Vec::new()));
                symbol2 = format!("{s}{}", "'".repeat(shadows.len() - 1)).into();
                let symbol_with_astrophes = symbol2.clone();
                // Temporarily overwrite symbol name for children
                std::mem::swap(s, &mut symbol2);
                let rest = self.print_flat(t, symbols);
                format!(
                    "<span style=\"color: {body_color}\">\
                    λ{symbol_with_astrophes}.\
                    </span>\
                    {rest}"
                )
            }
            Application(t1, t2, parenthesis_color, _) => {
                let t1 = *t1; // Yes, borrow checker is this stupid
                let t2 = *t2;
                let parenthesis_color = PARENTHESIS_COLORS[*parenthesis_color];
                format!(
                    "<span style=\"color: {parenthesis_color}\">\
                    (\
                    </span>\
                    {} {}\
                    <span style=\"color: {parenthesis_color}\">\
                    )\
                    </span>",
                    self.print_flat(t1, symbols),
                    self.print_flat(t2, symbols),
                )
            }
            Symbol(backref) => {
                let backref = *backref;
                match self.t.get(backref).unwrap() {
                    Definition(s, _, _, body_color) => format!(
                        "<span style=\"color: {}\">\
                        {s}\
                        </span>", BODY_COLORS[*body_color]
                    ),
                    _ => panic!(),
                }
            }
        };
        // If Definition match-arm was taken, return temporal symbol overwrite (x x') back to normal
        // This would be in the Definiton match-arm, but borrow checker wants it separate.
        if let Definition(s, _, _, _) = self.t.get_mut(node).unwrap() {
            std::mem::swap(s, &mut symbol2);
            symbols.get_mut(s).unwrap().pop();
        }
        out
    }

    // I called after create_leaf has added symbols to the table
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
            Definition(_, refs, c, _) => {
                *refs = references;
                *c = child
            },
            _ => panic!(),
        };
        alloc
    }

    fn create_leaf(
        &mut self,
        symbol: &CompactString,
        symbols: &mut Symbols,
        back_ref: Option<DefaultKey>,
        output: &mut String,
    ) -> Res<DefaultKey> {
        let alloc = self.t.insert(Symbol(null()));
        let (def_node, def_symbols) = match symbols.get_mut(symbol) {
            Some(s) => { // Symbol is found from local tree (parse / deep_clone)
                let (a, b) = s.last_mut().unwrap();
                (*a, b)
            },
            None => match back_ref { // Symbol is found from an outside context (deep_clone)
                Some(back_ref) => {
                    match self.t.get_mut(back_ref).unwrap() {
                        Definition(_, ss, _, _) => (back_ref, ss),
                        _ => panic!(),
                    }
                }
                None => { // Replace symbol with definition. Executed only when parsing
                    match self.bindings.get(symbol) {
                        Some(ast) => {
                            self.t.remove(alloc); // Useless alloc-dealloc :/
                            return self.deep_clone(*ast, &mut HashMap::new(), output)
                        }
                        None => {
                            writeln!(
                                output,
                                "Error: Unknown symbol '{symbol}'.\n\
                                Note: If you tried to make a call like 'λfx.f x', it's invalid. \
                                Wrap it like so: 'λfx.(f x).",
                            ).unwrap();
                            return Err(())
                        }
                    }
                }
            }
        };
        def_symbols.push(alloc);
        match self.t.get_mut(alloc).unwrap() {
            Symbol(p) => {*p = def_node},
            _ => panic!()
        };
        Ok(alloc)
    }

    fn parse(
        &mut self,
        source_code: &str,
        print: bool,
        output: &mut String,
        body_color: usize
    ) -> Res<DefaultKey> {

        if source_code.trim().is_empty() {
            writeln!(
                output,
                "Empty program rejected because it would be confusing \
                 to have no output on button press."
            ).unwrap();
            return Err(())
        }

        let mut symbols = Symbols::new();
        let re = Regex::new(r"([()])|(λ\s*[^()λ\.]+)\.|([^()λ\.\s\r\n]+)").unwrap();
        let mut tokens = re.captures_iter(source_code).map(|c| c.extract::<1>().1[0]).peekable();
        let parsed = self.parse_rec(&mut tokens, &mut symbols, 0, print, output, body_color)?;
        if let Some(tok) = tokens.next() {
            writeln!(
                output,
                "Error: Unexpected token '{tok}': Expected only one (possibly nested) expression,\n\
                found more. If you tried to make an evaluation, wrap parenthesis around it.\n\
                For example 'λfx.f x' is invalid syntax, make it 'λfx.(f x).' \n\
                Or, it may be that you have one extra closing parenthesis somewhere in your code."
            ).unwrap();
            return Err(())
        }
        Ok(parsed)
    }

    fn parse_rec<'a>(
        &mut self,
        tokens: &mut Peekable<impl Iterator<Item = &'a str>>,
        symbols: &mut Symbols,
        i: usize,
        print: bool,
        output: &mut String,
        body_color: usize,
    ) -> Res<DefaultKey> {
        let token = tokens.next()
            .ok_or_else(|| writeln!(output, "Closing parenthesis missing").unwrap())?;
        let next_char = token.chars().next().unwrap();
        let ind = " ".repeat(4 * (i+1));

        if next_char == 'λ' {
            let params = token[2..].trim().chars().filter(|c| !c.is_whitespace());

            let mut applications = Vec::new();
            for s in params {
                let mut symbol = CompactString::new(""); symbol.push(s); // Rust sucks,
                if print {
                    writeln!(
                        output,
                        "{ind}\
                        <span style=\"color: {}\">\
                            λ{symbol}\
                        </span>",
                        BODY_COLORS[body_color]
                    ).unwrap();
                }
                let alloc = self.t.insert(
                    Definition(symbol.clone(), Vec::new(), null(), body_color)
                );
                symbols.entry(symbol.clone()).or_default().push((alloc, Vec::new()));
                applications.push((symbol, alloc));
            }

            let mut child = self.parse_rec(tokens, symbols, i+1, print, output, body_color)?;

            for (symbol, alloc) in applications.iter().rev() {
                self.collect_symbols(*alloc, child, symbol, symbols);
                child = *alloc;
            }
            Ok(child)
        } else if next_char == '(' {
            let parenthesis_color = PARENTHESIS_COLORS[i % PARENTHESIS_COLORS.len()];
            if print {
                writeln!(
                    output,
                    "{ind}\
                    <span style=\"color: {parenthesis_color}\">\
                        (\
                    </span>"
                ).unwrap();
            }
            let mut left = self.parse_rec(tokens, symbols, i+1, print, output, body_color)?;
            let mut arguments = Vec::new();

            while *tokens.peek()
                .ok_or_else(|| writeln!(output, "Closing parenthesis missing").unwrap())?
                != ")"
            {
                arguments.push(self.parse_rec(tokens, symbols, i+1, print, output, body_color)?);
            }
            let ast = if arguments.is_empty() {
                left// Only one expression: no need to wrap it
            } else {
                for argument in arguments {
                    left = self.t.insert(
                        Application(left, argument, i % PARENTHESIS_COLORS.len(), body_color)
                    );
                }
                left
            };

            if print {
                writeln!(
                    output,
                    "{ind}\
                    <span style=\"color: {parenthesis_color}\">\
                        )\
                    </span>"
                ).unwrap();
            }
            assert_eq!(tokens.next(), Some(")"));
            Ok(ast)
        } else {
            let symbol: CompactString = token.into();
            if print {
                let body_color = match self.bindings.get(&symbol) {
                    Some(b) => {
                        match self.t.get(*b).unwrap() {
                            Definition(_, _, _, color) => *color,
                            Application(_, _, _, color) => *color,
                            _ => panic!(),
                        }
                    }
                    None => body_color
                };
                writeln!(
                    output,
                    "{ind}\
                    <span style=\"color: {}\">\
                        {symbol}\
                    </span>",
                    BODY_COLORS[body_color]
                ).unwrap();
            }
            self.create_leaf(&symbol, symbols, None, output)
        }
    }

    fn beta_reduce(
        &mut self,
        node: DefaultKey,
        parent: DefaultKey,
        argument: Option<(DefaultKey, DefaultKey)>,
        output: &mut String,
    ) -> Res<bool> {
        match self.t.get(node).unwrap().clone() {
            Definition(_, symbols, n, _) => {
                match argument {
                    None => {
                        self.beta_reduce(n, node, None, output)
                    }
                    Some((arg, grand_parent)) => {
                        for (i, reference) in symbols.iter().enumerate() {
                            let (arg_copied, arg_addr) = if i < symbols.len() - 1 {
                                let cloned = self.deep_clone(arg, &mut HashMap::new(), output)?;
                                (self.t.remove(cloned).unwrap(), cloned) // alloc + dealloc :/
                            } else {
                                (self.t.remove(arg).unwrap(), arg)
                            };

                            match &arg_copied {
                                Definition(_, ss, _, _) => {
                                    for s in ss{
                                        match self.t.get_mut(*s).unwrap() {
                                            Symbol(br) => {*br = *reference}
                                            _ => panic!(),
                                        }
                                    }
                                }
                                Symbol(back_ref) => {
                                    match self.t.get_mut(*back_ref).unwrap() {
                                        Definition(_, ss, _, _) => {
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
                            Definition(_, _, t, _) => {*t = n}
                            Application(t1, t2, _, _) => {
                                if *t1 == parent {*t1 = n;} else {*t2 = n;}
                            }
                            _ => panic!(),
                        }
                        self.t.remove(node).unwrap();
                        self.t.remove(parent).unwrap();
                        Ok(true)
                    }
                }
            }
            Application(t1, t2, _, _) => {
                let parn = Some((t2, parent));
                // Leftmost outermost reduction is guaranteed to yield beta-normal form, if exists
                let left = self.beta_reduce(t1, node, parn, output)?;
                Ok(left || self.beta_reduce(t2, node, None, output)?)
            },
            Symbol(_back_ref) => {
                Ok(false)
            },
        }
    }

    fn deep_clone(
        &mut self,
        key: DefaultKey,
        symbols: &mut Symbols,
        output: &mut String,
    ) -> Res<DefaultKey> {
        match self.t.get(key).unwrap() {
            Definition(symbol, _, t, c) => {
                let (symbol, t) = (symbol.clone(), *t); // Rust iz funy laguane
                let alloc = self.t.insert(Definition(symbol.clone(), Vec::new(), null(), *c));
                symbols.entry(symbol.clone()).or_default().push((alloc, Vec::new()));
                let child = self.deep_clone(t, symbols, output)?;
                Ok(self.collect_symbols(alloc, child, &symbol, symbols))
            }
            Application(t1, t2, pc, bc) => {
                let (t1, t2, pc, bc) = (*t1, *t2, *pc, *bc);
                let child1 = self.deep_clone(t1, symbols, output)?;
                let child2 = self.deep_clone(t2, symbols, output)?;
                Ok(self.t.insert(Application(child1, child2, pc, bc)))
            }
            Symbol(back_ref) => {
                let symbol = match self.t.get(*back_ref).unwrap() {
                    Definition(symbol, _, _, _) => symbol.clone(),
                    _ => panic!(),
                };
                self.create_leaf(&symbol, symbols, Some(*back_ref), output)
            }
        }
    }

    fn remove(&mut self, key: DefaultKey) {
        match self.t.get(key).unwrap() {
            Definition(_, _, t, _) => {
                self.remove(*t);
            }
            Application(t1, t2, _, _) => {
                let (t1, t2) = (*t1, *t2);  // Rust being rust
                self.remove(t1);
                self.remove(t2);
            }
            Symbol(back_ref) => {
                match self.t.get_mut(*back_ref).unwrap() {
                    Definition(_, ss, _, _) => {
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


    fn read_source_code(&mut self, source_code: &str, print: bool, output: &mut String) -> Res<()> {
        let mut position = 0;
        let mut parsing_in_statement = false;
        let mut color_counter = 0;

        for line_raw in source_code.split_inclusive('\n') {
            // Remove comments
            let line = match line_raw.find("#") {
                Some(n) => line_raw[0..n].trim(),
                None => line_raw.trim()
            };
            if line.is_empty() {
                position += line_raw.len();
                continue
            }
            if parsing_in_statement {
                break // Drops comments and empty lines between "in" and the expression
            }
            let (variable_name, the_rest) = match line.find("=") {
                Some(n) => (line[..n].trim(), line[n+1..].trim()),
                None => {
                    if line.trim() == "in" {
                        position += line_raw.len();
                        parsing_in_statement = true;
                        if print {
                            writeln!(output, "in").unwrap();
                        }
                        continue
                    } else if self.bindings.is_empty() {
                        break
                    } else {
                        writeln!(
                            output,
                            "Syntax error on line:\n{line}\nNo assignment \"=\" found.\n\
                            If this is your last expression, separate it from the definitions\
                            by adding \"in\" keyword."
                        ).unwrap();
                        return Err(())
                    }
                }
            };
            if variable_name.chars().any(|c| c.is_whitespace() || c == 'λ') {
                writeln!(output, "Error: Can not assign to '{variable_name}'").unwrap();
                return Err(())
            }

            if print {
                let body_color = BODY_COLORS[color_counter];
                writeln!(
                    output,
                    "<span style=\"color: {body_color}\">\
                        {variable_name} =\
                    </span>"
                ).unwrap();
            }
            let body = self.parse(the_rest, print, output, color_counter)?;
            self.bindings.insert(variable_name.into(), body);

            position += line_raw.len();
            color_counter = (color_counter + 1) % BODY_COLORS.len();
        }

        let last_lambda_expression = source_code[position..].trim();
        let head = self.parse(last_lambda_expression, print, output, 0)?;
        self.hat = self.t.insert(Definition("^".into(), Vec::new(), head, 0));
        Ok(())
    }
}

#[test]
fn test() {
    let inn = r"
true = λab.a
false = λab.b
and = λxy.(x y false)

# Numbers encoded as recursive function calls
0 = λfx.x
1 = λfx.(f x)
2 = λfx.(f (f x))
3 = λfx.(f (f (f x)))
4 = λfx.(f (f (f (f x))))
+1 = λnfx.(f (n f x))
-1 = λnfx.(n λgh.(h (g f)) (λu.x) (λu.u))

# Arithmetic
+ = λnmfx.((n f) (m f x))
* = λnmf.(m (n f))
- = λmn.(n -1 m)
^ = λnm.(m n)
↑↑ = λmn.((-1 n) (^ m) m)

# Pairs: x=first, y= second, h=head, t=tail
pair = λxyf.(f x y)
nil = false
fst = λl.(l λhtd.h nil)
snd = λl.(l λhtd.t nil)
is_nill = λl.(l λhtd.false true)

# Recursion with Y-combinator
u = λxy.(y (x x y))
Y = (u u)

# Factorial
if_0 = λn.((n λa.false) true)
factorial = λfn.(if_0 n 1 (* n (f (-1 n))))
! = (u u factorial)

# List processing
rfold = λfa.(Y (λrl.(l λhtd.(f (r t) h) a)))
map = λf.(rfold (λah.(pair (f h) a)) nil)
[1,2,3] = (pair 1 (pair 2 (pair 3 nil))

in
(rfold + 0 (map (^ 2) [1,2,3]))".to_string();
    process_input(&inn, true).unwrap();
}
